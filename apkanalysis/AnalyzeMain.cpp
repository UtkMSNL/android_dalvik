
#include "Dalvik.h"
#include "os/os.h"

#include <stdlib.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/resource.h>
#include <sys/mman.h>
#include <signal.h>
#include <errno.h>
#include <fcntl.h>

#ifdef HAVE_ANDROID_OS
#include <dirent.h>
#endif

#if defined(HAVE_PRCTL)
#include <sys/prctl.h>
#endif

#if defined(WITH_SELF_VERIFICATION)
#include "interp/Jit.h"         // need for self verification
#endif


/* desktop Linux needs a little help with gettid() */
#if defined(HAVE_GETTID) && !defined(HAVE_ANDROID_OS)
#define __KERNEL__
# include <linux/unistd.h>
#ifdef _syscall0
_syscall0(pid_t,gettid)
#else
pid_t gettid() { return syscall(__NR_gettid);}
#endif
#undef __KERNEL__
#endif

#define ZYGOTE_CLASS_CUTOFF 2304
#define CLASS_SFIELD_SLOTS 1
#define INITIAL_CLASS_SERIAL_NUMBER 0x50000000

static void threadExitCheck(void* arg)
{
    const int kMaxCount = 2;

    Thread* self = (Thread*) arg;
    assert(self != NULL);

    ALOGV("threadid=%d: threadExitCheck(%p) count=%d",
        self->threadId, arg, self->threadExitCheckCount);

    if (self->status == THREAD_ZOMBIE) {
        ALOGW("threadid=%d: Weird -- shouldn't be in threadExitCheck",
            self->threadId);
        return;
    }

    if (self->threadExitCheckCount < kMaxCount) {
        /*
         * Spin a couple of times to let other destructors fire.
         */
        ALOGD("threadid=%d: thread exiting, not yet detached (count=%d)",
            self->threadId, self->threadExitCheckCount);
        self->threadExitCheckCount++;
        int cc = pthread_setspecific(gDvm.pthreadKeySelf, self);
        if (cc != 0) {
            ALOGE("threadid=%d: unable to re-add thread to TLS",
                self->threadId);
            dvmAbort();
        }
    } else {
        ALOGE("threadid=%d: native thread exited without detaching",
            self->threadId);
        dvmAbort();
    }
}

static Thread* allocThread(int interpStackSize)
{
    Thread* thread;
    u1* stackBottom;

    thread = (Thread*) calloc(1, sizeof(Thread));
    if (thread == NULL)
        return NULL;

    /* Check sizes and alignment */
    assert((((uintptr_t)&thread->interpBreak.all) & 0x7) == 0);
    assert(sizeof(thread->interpBreak) == sizeof(thread->interpBreak.all));


#if defined(WITH_SELF_VERIFICATION)
    if (dvmSelfVerificationShadowSpaceAlloc(thread) == NULL)
        return NULL;
#endif

    assert(interpStackSize >= kMinStackSize && interpStackSize <=kMaxStackSize);

    thread->status = THREAD_INITIALIZING;

    /*
     * Allocate and initialize the interpreted code stack.  We essentially
     * "lose" the alloc pointer, which points at the bottom of the stack,
     * but we can get it back later because we know how big the stack is.
     *
     * The stack must be aligned on a 4-byte boundary.
     */
#ifdef MALLOC_INTERP_STACK
    stackBottom = (u1*) malloc(interpStackSize);
    if (stackBottom == NULL) {
#if defined(WITH_SELF_VERIFICATION)
        dvmSelfVerificationShadowSpaceFree(thread);
#endif
        free(thread);
        return NULL;
    }
    memset(stackBottom, 0xc5, interpStackSize);     // stop valgrind complaints
#else
    stackBottom = (u1*) mmap(NULL, interpStackSize, PROT_READ | PROT_WRITE,
        MAP_PRIVATE | MAP_ANON, -1, 0);
    if (stackBottom == MAP_FAILED) {
#if defined(WITH_SELF_VERIFICATION)
        dvmSelfVerificationShadowSpaceFree(thread);
#endif
        free(thread);
        return NULL;
    }
#endif

    assert(((u4)stackBottom & 0x03) == 0); // looks like our malloc ensures this
    thread->interpStackSize = interpStackSize;
    thread->interpStackStart = stackBottom + interpStackSize;
    thread->interpStackEnd = stackBottom + STACK_OVERFLOW_RESERVE;

#ifndef DVM_NO_ASM_INTERP
    thread->mainHandlerTable = dvmAsmInstructionStart;
    thread->altHandlerTable = dvmAsmAltInstructionStart;
    thread->interpBreak.ctl.curHandlerTable = thread->mainHandlerTable;
#endif

    /* give the thread code a chance to set things up */
    dvmInitInterpStack(thread, interpStackSize);

    /* One-time setup for interpreter/JIT state */
    dvmInitInterpreterState(thread);

#ifdef WITH_OFFLOAD
    thread->offDaemon = false;
    thread->offGhost = gDvm.isServer && gDvm.initializing;
    thread->offLocalOnly = true;
    thread->offLocal = true;
    thread->breakFrames = 0;
    thread->migrationCounter = 0;
    thread->offDeactivateBreakFrames = 0;
    thread->offFlagMigration = false;
    thread->offFlagDeath = false;
    thread->offTrimSignaled = false;
    thread->offWriteBuffer = auxFifoCreate();
    thread->offReadBuffer = auxFifoCreate();
    pthread_mutex_init(&thread->offBufferLock, NULL);
    pthread_cond_init(&thread->offBufferCond, NULL);
    thread->offCorkLevel = 0;
    thread->offProtection = 0;


    memset(thread->offLockList, 0, sizeof(thread->offLockList));
#endif

    return thread;
}

static size_t classObjectSize(size_t sfieldCount)
{
    size_t offset = OFFSETOF_MEMBER(ClassObject, sfields);
    return offset + sizeof(StaticField) * sfieldCount;
}

ClassObject* dvmFindPrimitiveClass(char type)
{
    PrimitiveType primitiveType = dexGetPrimitiveTypeFromDescriptorChar(type);

    switch (primitiveType) {
        case PRIM_VOID:    return gDvm.typeVoid;
        case PRIM_BOOLEAN: return gDvm.typeBoolean;
        case PRIM_BYTE:    return gDvm.typeByte;
        case PRIM_SHORT:   return gDvm.typeShort;
        case PRIM_CHAR:    return gDvm.typeChar;
        case PRIM_INT:     return gDvm.typeInt;
        case PRIM_LONG:    return gDvm.typeLong;
        case PRIM_FLOAT:   return gDvm.typeFloat;
        case PRIM_DOUBLE:  return gDvm.typeDouble;
        default: {
            ALOGW("Unknown primitive type '%c'", type);
            return NULL;
        }
    }
}

/*
 * Synthesize a primitive class.
 *
 * Just creates the class and returns it (does not add it to the class list).
 */
static bool createPrimitiveType(PrimitiveType primitiveType, ClassObject** pClass)
{
    /*
     * Fill out a few fields in the ClassObject.
     *
     * Note that primitive classes do not sub-class the class Object.
     * This matters for "instanceof" checks. Also, we assume that the
     * primitive class does not override finalize().
     */

    const char* descriptor = dexGetPrimitiveTypeDescriptor(primitiveType);
    assert(descriptor != NULL);

    ClassObject* newClass = (ClassObject*) dvmMalloc(sizeof(*newClass), ALLOC_NON_MOVING);
    if (newClass == NULL) {
        return false;
    }

    DVM_OBJECT_INIT(newClass, gDvm.classJavaLangClass);
    dvmSetClassSerialNumber(newClass);
    SET_CLASS_FLAG(newClass, ACC_PUBLIC | ACC_FINAL | ACC_ABSTRACT);
    newClass->primitiveType = primitiveType;
    newClass->descriptorAlloc = NULL;
    newClass->descriptor = descriptor;
    newClass->super = NULL;
    newClass->status = CLASS_INITIALIZED;

#ifdef WITH_OFFLOAD
    newClass->objId = offClassToId(newClass);
    newClass->offInfo.obj = (Object*)newClass;
    newClass->offInfo.dirty = 0;
    newClass->offInfo.bits = NULL;
    newClass->offInfo.isVolatileOwner =
        newClass->offInfo.isLockOwner = !gDvm.isServer;
    newClass->offInfo.isQueued = false;
#endif

    /* don't need to set newClass->objectSize */

    LOGVV("Constructed class for primitive type '%s'", newClass->descriptor);

    *pClass = newClass;
    dvmReleaseTrackedAlloc((Object*) newClass, NULL);

    return true;
}

/*
 * Create the initial class instances. These consist of the class
 * Class and all of the classes representing primitive types.
 */
static bool createInitialClasses() {
    /*
     * Initialize the class Class. This has to be done specially, particularly
     * because it is an instance of itself.
     */
    ClassObject* clazz = (ClassObject*)
        dvmMalloc(classObjectSize(CLASS_SFIELD_SLOTS), ALLOC_NON_MOVING);
    if (clazz == NULL) {
        return false;
    }
    DVM_OBJECT_INIT(clazz, clazz);
    SET_CLASS_FLAG(clazz, ACC_PUBLIC | ACC_FINAL | CLASS_ISCLASS);
    clazz->descriptor = "Ljava/lang/Class;";
    gDvm.classJavaLangClass = clazz;
    LOGVV("Constructed the class Class.");

    /*
     * Initialize the classes representing primitive types. These are
     * instances of the class Class, but other than that they're fairly
     * different from regular classes.
     */
    bool ok = true;
    ok &= createPrimitiveType(PRIM_VOID,    &gDvm.typeVoid);
    ok &= createPrimitiveType(PRIM_BOOLEAN, &gDvm.typeBoolean);
    ok &= createPrimitiveType(PRIM_BYTE,    &gDvm.typeByte);
    ok &= createPrimitiveType(PRIM_SHORT,   &gDvm.typeShort);
    ok &= createPrimitiveType(PRIM_CHAR,    &gDvm.typeChar);
    ok &= createPrimitiveType(PRIM_INT,     &gDvm.typeInt);
    ok &= createPrimitiveType(PRIM_LONG,    &gDvm.typeLong);
    ok &= createPrimitiveType(PRIM_FLOAT,   &gDvm.typeFloat);
    ok &= createPrimitiveType(PRIM_DOUBLE,  &gDvm.typeDouble);

    return ok;
}

int main(int argc, char** argv) {
    //if(argc != 2 && argc != 3) {
    //    printf("apkanalysis -option [ApkPath]]\n");
    //    return 0;
    //}
    /* allocate a TLS slot */
    if (pthread_key_create(&gDvm.pthreadKeySelf, threadExitCheck) != 0) {
        ALOGE("ERROR: pthread_key_create failed");
        return false;
    }

    /* test our pthread lib */
    if (pthread_getspecific(gDvm.pthreadKeySelf) != NULL)
        ALOGW("WARNING: newly-created pthread TLS slot is not NULL");

    /* prep thread-related locks and conditions */
    dvmInitMutex(&gDvm.threadListLock);
    pthread_cond_init(&gDvm.threadStartCond, NULL);
    pthread_cond_init(&gDvm.vmExitCond, NULL);
    dvmInitMutex(&gDvm._threadSuspendLock);
    dvmInitMutex(&gDvm.threadSuspendCountLock);
    pthread_cond_init(&gDvm.threadSuspendCountCond, NULL);

    gDvm.threadSleepMon = dvmCreateMonitor(NULL);
    
    JavaVMAttachArgs jniArgs;

    jniArgs.version = JNI_VERSION_1_2;
    jniArgs.name = "fakevm";
    gDvm.stackSize = kDefaultStackSize;
    gDvm.mainThreadStackSize = kDefaultStackSize;
    gDvm.threadIdMap = dvmAllocBitVector(((1 << 16) - 1), false);
    gDvm.offThreadTable = dvmHashTableCreate(32, NULL);
    //dvmThreadStartup();
    //dvmPrepMainThread();

    //jniArgs.group = reinterpret_cast<jobject>(pArgs->group);
   // dvmAttachCurrentThread(&jniArgs, false);
    Thread* thread = NULL;
    bool ok;

    /* allocate thread struct, and establish a basic sense of self */
    thread = allocThread(gDvm.stackSize);
    if (thread == NULL)
        return -1;

    /*
     * Finish our thread prep.  We need to do this before adding ourselves
     * to the thread list or invoking any interpreted code.  prepareThread()
     * requires that we hold the thread list lock.
     */
    dvmLockThreadList(thread);
    thread->threadId = 5;
    thread->handle = pthread_self();
    thread->systemTid = dvmGetSysThreadId();
    int cc;
    cc = pthread_setspecific(gDvm.pthreadKeySelf, thread);
    if (cc != 0) {
        if (thread != NULL) {
            ALOGE("pthread_setspecific(%p) failed, err=%d", thread, cc);
            dvmAbort();     /* the world is fundamentally hosed */
        }
    }

    /*
     * Initialize invokeReq.
     */
    dvmInitMutex(&thread->invokeReq.lock);
    pthread_cond_init(&thread->invokeReq.cv, NULL);

    /*
     * Initialize our reference tracking tables.
     *
     * Most threads won't use jniMonitorRefTable, so we clear out the
     * structure but don't call the init function (which allocs storage).
     */
    if (!thread->jniLocalRefTable.init(kJniLocalRefMin,
            kJniLocalRefMax, kIndirectKindLocal)) {
        return -1;
    }
    if (!dvmInitReferenceTable(&thread->internalLocalRefTable,
            kInternalRefDefault, kInternalRefMax))
        return -1;

    memset(&thread->jniMonitorRefTable, 0, sizeof(thread->jniMonitorRefTable));

    pthread_cond_init(&thread->waitCond, NULL);
    dvmInitMutex(&thread->waitMutex);

    /* Initialize safepoint callback mechanism */
    dvmInitMutex(&thread->callbackMutex);
    thread->status = THREAD_RUNNING;
    dvmUnlockThreadList();    
    gDvm.heapStartingSize = 100 * 1024 * 1024;
    gDvm.heapMaximumSize = 200 * 1024 * 1024;
    gDvm.heapGrowthLimit = 200 * 1024 * 1024;
    
    dvmHeapStartup();
    
    gDvm.loadedClasses = dvmHashTableCreate(256, (HashFreeFunc) dvmFreeClassInnards);
    gDvm.classSerialNumber = INITIAL_CLASS_SERIAL_NUMBER;
    gDvm.pBootLoaderAlloc = dvmLinearAllocCreate(NULL);
    gDvm.initiatingLoaderList = (InitiatingLoaderList*)
        calloc(ZYGOTE_CLASS_CUTOFF, sizeof(InitiatingLoaderList));
    if (!createInitialClasses()) {
        return -1;
    }
    
    gDvm.offRulesHash = dvmHashTableCreate(256, free);
    offControlStartup(false);
    dvmInstanceofStartup();
    
    if(strcmp(argv[1], "-s")) {
        char* apkPath = argv[1];
        char* flag = argv[2];
        int maxSubClass = atoi(argv[3]);
        loadApk(apkPath, flag, maxSubClass);
    } else {
        char* apkPath = argv[2];
        char* flag = argv[3];
        int maxSubClass = atoi(argv[4]);
        loadApkStatic(apkPath, flag, maxSubClass);
    }
    printf("apk analysis complete");
}
