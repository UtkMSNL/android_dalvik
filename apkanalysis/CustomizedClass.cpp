/*
 * Copyright (C) 2008 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * Class loading, including bootstrap class loader, linking, and
 * initialization.
 */

#define LOG_CLASS_LOADING 0

#include "Dalvik.h"
#include "libdex/DexClass.h"
#include "analysis/Optimize.h"

#include <stdlib.h>
#include <stddef.h>
#include <sys/stat.h>

#if LOG_CLASS_LOADING
#include <unistd.h>
#include <pthread.h>
#include <cutils/process_name.h>
#include <sys/types.h>
#endif

/*
Notes on Linking and Verification

The basic way to retrieve a class is to load it, make sure its superclass
and interfaces are available, prepare its fields, and return it.  This gets
a little more complicated when multiple threads can be trying to retrieve
the class simultaneously, requiring that we use the class object's monitor
to keep things orderly.

The linking (preparing, resolving) of a class can cause us to recursively
load superclasses and interfaces.  Barring circular references (e.g. two
classes that are superclasses of each other), this will complete without
the loader attempting to access the partially-linked class.

With verification, the situation is different.  If we try to verify
every class as we load it, we quickly run into trouble.  Even the lowly
java.lang.Object requires CloneNotSupportedException; follow the list
of referenced classes and you can head down quite a trail.  The trail
eventually leads back to Object, which is officially not fully-formed yet.

The VM spec (specifically, v2 5.4.1) notes that classes pulled in during
verification do not need to be prepared or verified.  This means that we
are allowed to have loaded but unverified classes.  It further notes that
the class must be verified before it is initialized, which allows us to
defer verification for all classes until class init.  You can't execute
code or access fields in an uninitialized class, so this is safe.

It also allows a more peaceful coexistence between verified and
unverifiable code.  If class A refers to B, and B has a method that
refers to a bogus class C, should we allow class A to be verified?
If A only exercises parts of B that don't use class C, then there is
nothing wrong with running code in A.  We can fully verify both A and B,
and allow execution to continue until B causes initialization of C.  The
VerifyError is thrown close to the point of use.

This gets a little weird with java.lang.Class, which is the only class
that can be instantiated before it is initialized.  We have to force
initialization right after the class is created, because by definition we
have instances of it on the heap, and somebody might get a class object and
start making virtual calls on it.  We can end up going recursive during
verification of java.lang.Class, but we avoid that by checking to see if
verification is already in progress before we try to initialize it.
*/

/*
Notes on class loaders and interaction with optimization / verification

In what follows, "pre-verification" and "optimization" are the steps
performed by the dexopt command, which attempts to verify and optimize
classes as part of unpacking jar files and storing the DEX data in the
dalvik-cache directory.  These steps are performed by loading the DEX
files directly, without any assistance from ClassLoader instances.

When we pre-verify and optimize a class in a DEX file, we make some
assumptions about where the class loader will go to look for classes.
If we can't guarantee those assumptions, e.g. because a class ("AppClass")
references something not defined in the bootstrap jars or the AppClass jar,
we can't pre-verify or optimize the class.

The VM doesn't define the behavior of user-defined class loaders.
For example, suppose application class AppClass, loaded by UserLoader,
has a method that creates a java.lang.String.  The first time
AppClass.stringyMethod tries to do something with java.lang.String, it
asks UserLoader to find it.  UserLoader is expected to defer to its parent
loader, but isn't required to.  UserLoader might provide a replacement
for String.

We can run into trouble if we pre-verify AppClass with the assumption that
java.lang.String will come from core.jar, and don't verify this assumption
at runtime.  There are two places that an alternate implementation of
java.lang.String can come from: the AppClass jar, or from some other jar
that UserLoader knows about.  (Someday UserLoader will be able to generate
some bytecode and call DefineClass, but not yet.)

To handle the first situation, the pre-verifier will explicitly check for
conflicts between the class being optimized/verified and the bootstrap
classes.  If an app jar contains a class that has the same package and
class name as a class in a bootstrap jar, the verification resolver refuses
to find either, which will block pre-verification and optimization on
classes that reference ambiguity.  The VM will postpone verification of
the app class until first load.

For the second situation, we need to ensure that all references from a
pre-verified class are satisified by the class' jar or earlier bootstrap
jars.  In concrete terms: when resolving a reference to NewClass,
which was caused by a reference in class AppClass, we check to see if
AppClass was pre-verified.  If so, we require that NewClass comes out
of either the AppClass jar or one of the jars in the bootstrap path.
(We may not control the class loaders, but we do manage the DEX files.
We can verify that it's either (loader==null && dexFile==a_boot_dex)
or (loader==UserLoader && dexFile==AppClass.dexFile).  Classes from
DefineClass can't be pre-verified, so this doesn't apply.)

This should ensure that you can't "fake out" the pre-verifier by creating
a user-defined class loader that replaces system classes.  It should
also ensure that you can write such a loader and have it work in the
expected fashion; all you lose is some performance due to "just-in-time
verification" and the lack of DEX optimizations.

There is a "back door" of sorts in the class resolution check, due to
the fact that the "class ref" entries are shared between the bytecode
and meta-data references (e.g. annotations and exception handler lists).
The class references in annotations have no bearing on class verification,
so when a class does an annotation query that causes a class reference
index to be resolved, we don't want to fail just because the calling
class was pre-verified and the resolved class is in some random DEX file.
The successful resolution adds the class to the "resolved classes" table,
so when optimized bytecode references it we don't repeat the resolve-time
check.  We can avoid this by not updating the "resolved classes" table
when the class reference doesn't come out of something that has been
checked by the verifier, but that has a nonzero performance impact.
Since the ultimate goal of this test is to catch an unusual situation
(user-defined class loaders redefining core classes), the added caution
may not be worth the performance hit.
*/

/*
 * Class serial numbers start at this value.  We use a nonzero initial
 * value so they stand out in binary dumps (e.g. hprof output).
 */
#define INITIAL_CLASS_SERIAL_NUMBER 0x50000000

/*
 * Constant used to size an auxillary class object data structure.
 * For optimum memory use this should be equal to or slightly larger than
 * the number of classes loaded when the zygote finishes initializing.
 */
#define ZYGOTE_CLASS_CUTOFF 2304

#define CLASS_SFIELD_SLOTS 1

static ClassObject* findClassNoInit(const char* descriptor, Object* loader,\
    DvmDex* pDvmDex);
static ClassObject* loadClassFromDex(DvmDex* pDvmDex,
    const DexClassDef* pClassDef, Object* loader);
static void loadMethodFromDex(ClassObject* clazz, const DexMethod* pDexMethod,\
    Method* meth);
static int computeJniArgInfo(const DexProto* proto);
static void loadSFieldFromDex(ClassObject* clazz,
    const DexField* pDexSField, StaticField* sfield);
static void loadIFieldFromDex(ClassObject* clazz,
    const DexField* pDexIField, InstField* field);
static bool precacheReferenceOffsets(ClassObject* clazz);
static void computeRefOffsets(ClassObject* clazz);
static bool createVtable(ClassObject* clazz);
static bool createIftable(ClassObject* clazz);
static bool insertMethodStubs(ClassObject* clazz);
static bool computeFieldOffsets(ClassObject* clazz);
static void throwEarlierClassFailure(ClassObject* clazz);
static bool customLinkClass(ClassObject* clazz);

static size_t classObjectSize(size_t sfieldCount)
{
    size_t offset = OFFSETOF_MEMBER(ClassObject, sfields);
    return offset + sizeof(StaticField) * sfieldCount;
}

/*
 * Remove a class object from the hash table.
 */
static void removeClassFromHash(ClassObject* clazz)
{
    ALOGV("+++ removeClassFromHash '%s'", clazz->descriptor);

    u4 hash = dvmComputeUtf8Hash(clazz->descriptor);

    dvmHashTableLock(gDvm.loadedClasses);
    if (!dvmHashTableRemove(gDvm.loadedClasses, hash, clazz))
        ALOGW("Hash table remove failed on class '%s'", clazz->descriptor);
    dvmHashTableUnlock(gDvm.loadedClasses);
}

/*
 * Search the DEX files we loaded from the bootstrap class path for a DEX
 * file that has the class with the matching descriptor.
 *
 * Returns the matching DEX file and DexClassDef entry if found, otherwise
 * returns NULL.
 */
static DvmDex* searchBootPathForClass(const char* descriptor,
    const DexClassDef** ppClassDef)
{
    const ClassPathEntry* cpe = gDvm.bootClassPath;
    const DexClassDef* pFoundDef = NULL;
    DvmDex* pFoundFile = NULL;

    LOGVV("+++ class '%s' not yet loaded, scanning bootclasspath...",
        descriptor);

    while (cpe->kind != kCpeLastEntry) {
        //ALOGV("+++  checking '%s' (%d)", cpe->fileName, cpe->kind);

        switch (cpe->kind) {
        case kCpeJar:
            {
                JarFile* pJarFile = (JarFile*) cpe->ptr;
                const DexClassDef* pClassDef;
                DvmDex* pDvmDex;

                pDvmDex = dvmGetJarFileDex(pJarFile);
                pClassDef = dexFindClass(pDvmDex->pDexFile, descriptor);
                if (pClassDef != NULL) {
                    /* found */
                    pFoundDef = pClassDef;
                    pFoundFile = pDvmDex;
                    goto found;
                }
            }
            break;
        case kCpeDex:
            {
                RawDexFile* pRawDexFile = (RawDexFile*) cpe->ptr;
                const DexClassDef* pClassDef;
                DvmDex* pDvmDex;

                pDvmDex = dvmGetRawDexFileDex(pRawDexFile);
                pClassDef = dexFindClass(pDvmDex->pDexFile, descriptor);
                if (pClassDef != NULL) {
                    /* found */
                    pFoundDef = pClassDef;
                    pFoundFile = pDvmDex;
                    goto found;
                }
            }
            break;
        default:
            ALOGE("Unknown kind %d", cpe->kind);
            assert(false);
            break;
        }

        cpe++;
    }

    /*
     * Special handling during verification + optimization.
     *
     * The DEX optimizer needs to load classes from the DEX file it's working
     * on.  Rather than trying to insert it into the bootstrap class path
     * or synthesizing a class loader to manage it, we just make it available
     * here.  It logically comes after all existing entries in the bootstrap
     * class path.
     */
    if (gDvm.bootClassPathOptExtra != NULL) {
        const DexClassDef* pClassDef;

        pClassDef =
            dexFindClass(gDvm.bootClassPathOptExtra->pDexFile, descriptor);
        if (pClassDef != NULL) {
            /* found */
            pFoundDef = pClassDef;
            pFoundFile = gDvm.bootClassPathOptExtra;
        }
    }

found:
    *ppClassDef = pFoundDef;
    return pFoundFile;
}

/*
 * Find a resource with the specified name in entry N of the boot class path.
 *
 * We return a newly-allocated String of one of these forms:
 *   file://path/name
 *   jar:file://path!/name
 * Where "path" is the bootstrap class path entry and "name" is the string
 * passed into this method.  "path" needs to be an absolute path (starting
 * with '/'); if it's not we'd need to "absolutify" it as part of forming
 * the URL string.
 */
StringObject* dvmGetBootPathResource(const char* name, int idx)
{
    const int kUrlOverhead = 13;        // worst case for Jar URL
    const ClassPathEntry* cpe = gDvm.bootClassPath;
    StringObject* urlObj = NULL;

    ALOGV("+++ searching for resource '%s' in %d(%s)",
        name, idx, cpe[idx].fileName);

    /* we could use direct array index, but I don't entirely trust "idx" */
    while (idx-- && cpe->kind != kCpeLastEntry)
        cpe++;
    if (cpe->kind == kCpeLastEntry) {
        assert(false);
        return NULL;
    }

    char urlBuf[strlen(name) + strlen(cpe->fileName) + kUrlOverhead +1];

    switch (cpe->kind) {
    case kCpeJar:
        {
            JarFile* pJarFile = (JarFile*) cpe->ptr;
            if (dexZipFindEntry(&pJarFile->archive, name) == NULL)
                goto bail;
            sprintf(urlBuf, "jar:file://%s!/%s", cpe->fileName, name);
        }
        break;
    case kCpeDex:
        ALOGV("No resources in DEX files");
        goto bail;
    default:
        assert(false);
        goto bail;
    }

    ALOGV("+++ using URL='%s'", urlBuf);
    urlObj = dvmCreateStringFromCstr(urlBuf);

bail:
    return urlObj;
}

/*
 * ===========================================================================
 *      Class list management
 * ===========================================================================
 */

/*
 * Load the named class (by descriptor) from the specified DEX file.
 * Used by class loaders to instantiate a class object from a
 * VM-managed DEX.
 */
ClassObject* customDefineClass(DvmDex* pDvmDex, const char* descriptor,
    Object* classLoader)
{
    assert(pDvmDex != NULL);

    return findClassNoInit(descriptor, classLoader, pDvmDex);
}

/*
 * Find the named class (by descriptor). If it's not already loaded,
 * we load it and link it, but don't execute <clinit>. (The VM has
 * specific limitations on which events can cause initialization.)
 *
 * If "pDexFile" is NULL, we will search the bootclasspath for an entry.
 *
 * On failure, this returns NULL with an exception raised.
 *
 * TODO: we need to return an indication of whether we loaded the class or
 * used an existing definition.  If somebody deliberately tries to load a
 * class twice in the same class loader, they should get a LinkageError,
 * but inadvertent simultaneous class references should "just work".
 */
static ClassObject* findClassNoInit(const char* descriptor, Object* loader,
    DvmDex* pDvmDex)
{
    Thread* self = dvmThreadSelf();
    ClassObject* clazz;
    bool profilerNotified = false;

    if (loader != NULL) {
        LOGVV("#### findClassNoInit(%s,%p,%p)", descriptor, loader,
            pDvmDex->pDexFile);
    }

    /*
     * We don't expect an exception to be raised at this point.  The
     * exception handling code is good about managing this.  This *can*
     * happen if a JNI lookup fails and the JNI code doesn't do any
     * error checking before doing another class lookup, so we may just
     * want to clear this and restore it on exit.  If we don't, some kinds
     * of failures can't be detected without rearranging other stuff.
     *
     * Most often when we hit this situation it means that something is
     * broken in the VM or in JNI code, so I'm keeping it in place (and
     * making it an informative abort rather than an assert).
     */
    if (dvmCheckException(self)) {
        ALOGE("Class lookup %s attempted with exception pending", descriptor);
        ALOGW("Pending exception is:");
        dvmLogExceptionStackTrace();
        dvmDumpAllThreads(false);
        dvmAbort();
    }

    clazz = dvmLookupClass(descriptor, loader, true);
    if (clazz == NULL) {
        const DexClassDef* pClassDef;

        dvmMethodTraceClassPrepBegin();
        profilerNotified = true;

#if LOG_CLASS_LOADING
        u8 startTime = dvmGetThreadCpuTimeNsec();
#endif

        if (pDvmDex == NULL) {
            assert(loader == NULL);     /* shouldn't be here otherwise */
            pDvmDex = searchBootPathForClass(descriptor, &pClassDef);
        } else {
            pClassDef = dexFindClass(pDvmDex->pDexFile, descriptor);
        }

        if (pDvmDex == NULL || pClassDef == NULL) {
            goto bail;
        }

        /* found a match, try to load it */
        clazz = loadClassFromDex(pDvmDex, pClassDef, loader);
        if (dvmCheckException(self)) {
            /* class was found but had issues */
            if (clazz != NULL) {
                dvmFreeClassInnards(clazz);
                dvmReleaseTrackedAlloc((Object*) clazz, NULL);
            }
            goto bail;
        }

        /*
         * Lock the class while we link it so other threads must wait for us
         * to finish.  Set the "initThreadId" so we can identify recursive
         * invocation.  (Note all accesses to initThreadId here are
         * guarded by the class object's lock.)
         */
        dvmLockObject(self, (Object*) clazz);
        clazz->initThreadId = self->threadId;

        /*
         * Add to hash table so lookups succeed.
         *
         * [Are circular references possible when linking a class?]
         */
        assert(clazz->classLoader == loader);
        if (!dvmAddClassToHash(clazz)) {
            /*
             * Another thread must have loaded the class after we
             * started but before we finished.  Discard what we've
             * done and leave some hints for the GC.
             *
             * (Yes, this happens.)
             */
            //ALOGW("WOW: somebody loaded %s simultaneously", descriptor);
            clazz->initThreadId = 0;
            dvmUnlockObject(self, (Object*) clazz);

            /* Let the GC free the class.
             */
            dvmFreeClassInnards(clazz);
            dvmReleaseTrackedAlloc((Object*) clazz, NULL);

            /* Grab the winning class.
             */
            clazz = dvmLookupClass(descriptor, loader, true);
            assert(clazz != NULL);
            goto got_class;
        }
        dvmReleaseTrackedAlloc((Object*) clazz, NULL);

#if LOG_CLASS_LOADING
        logClassLoadWithTime('>', clazz, startTime);
#endif
        /*
         * Prepare and resolve.
         */
        if (!customLinkClass(clazz)) {
            assert(dvmCheckException(self));

            /* Make note of the error and clean up the class.
             */
            removeClassFromHash(clazz);
            clazz->status = CLASS_ERROR;
            dvmFreeClassInnards(clazz);

            /* Let any waiters know.
             */
            clazz->initThreadId = 0;
            dvmObjectNotifyAll(self, (Object*) clazz);
            dvmUnlockObject(self, (Object*) clazz);

            clazz = NULL;
            if (gDvm.optimizing) {
                /* happens with "external" libs */
                ALOGV("Link of class '%s' failed", descriptor);
            } else {
                ALOGW("Link of class '%s' failed", descriptor);
            }
            goto bail;
        }
        
        dvmObjectNotifyAll(self, (Object*) clazz);
        dvmUnlockObject(self, (Object*) clazz);

        /*
         * Add class stats to global counters.
         *
         * TODO: these should probably be atomic ops.
         */
        gDvm.numLoadedClasses++;
        gDvm.numDeclaredMethods +=
            clazz->virtualMethodCount + clazz->directMethodCount;
        gDvm.numDeclaredInstFields += clazz->ifieldCount;
        gDvm.numDeclaredStaticFields += clazz->sfieldCount;

        /*
         * Cache pointers to basic classes.  We want to use these in
         * various places, and it's easiest to initialize them on first
         * use rather than trying to force them to initialize (startup
         * ordering makes it weird).
         */
        if (gDvm.classJavaLangObject == NULL &&
            strcmp(descriptor, "Ljava/lang/Object;") == 0)
        {
            /* It should be impossible to get here with anything
             * but the bootclasspath loader.
             */
            assert(loader == NULL);
            gDvm.classJavaLangObject = clazz;
        }

    } else {
got_class:
        if (!dvmIsClassLinked(clazz) && clazz->status != CLASS_ERROR) {
            /*
             * We can race with other threads for class linking.  We should
             * never get here recursively; doing so indicates that two
             * classes have circular dependencies.
             *
             * One exception: we force discovery of java.lang.Class in
             * dvmLinkClass(), and Class has Object as its superclass.  So
             * if the first thing we ever load is Object, we will init
             * Object->Class->Object.  The easiest way to avoid this is to
             * ensure that Object is never the first thing we look up, so
             * we get Foo->Class->Object instead.
             */
            dvmLockObject(self, (Object*) clazz);
            if (!dvmIsClassLinked(clazz) &&
                clazz->initThreadId == self->threadId)
            {
                ALOGW("Recursive link on class %s", clazz->descriptor);
                dvmUnlockObject(self, (Object*) clazz);
                dvmThrowClassCircularityError(clazz->descriptor);
                clazz = NULL;
                goto bail;
            }
            //ALOGI("WAITING  for '%s' (owner=%d)",
            //    clazz->descriptor, clazz->initThreadId);
            while (!dvmIsClassLinked(clazz) && clazz->status != CLASS_ERROR) {
                dvmObjectWait(self, (Object*) clazz, 0, 0, false);
            }
            dvmUnlockObject(self, (Object*) clazz);
        }
        if (clazz->status == CLASS_ERROR) {
            /*
             * Somebody else tried to load this and failed.  We need to raise
             * an exception and report failure.
             */
            throwEarlierClassFailure(clazz);
            clazz = NULL;
            goto bail;
        }
    }

    /* check some invariants */
    assert(dvmIsClassLinked(clazz));
    assert(gDvm.classJavaLangClass != NULL);
    assert(clazz->clazz == gDvm.classJavaLangClass);
    assert(dvmIsClassObject(clazz));
    // modified by Yong @May 21 to pass the check of new object which is the one loaded by my dex ---start
//comment this line    assert(clazz == gDvm.classJavaLangObject || clazz->super != NULL);
    // modified by Yong --- end
    if (!dvmIsInterfaceClass(clazz)) {
        //ALOGI("class=%s vtableCount=%d, virtualMeth=%d",
        //    clazz->descriptor, clazz->vtableCount,
        //    clazz->virtualMethodCount);
        assert(clazz->vtableCount >= clazz->virtualMethodCount);
    }

bail:
    if (profilerNotified)
        dvmMethodTraceClassPrepEnd();
    //assert(clazz != NULL || dvmCheckException(self));
    return clazz;
}

/*
 * Helper for loadClassFromDex, which takes a DexClassDataHeader and
 * encoded data pointer in addition to the other arguments.
 */
static ClassObject* loadClassFromDex0(DvmDex* pDvmDex,
    const DexClassDef* pClassDef, const DexClassDataHeader* pHeader,
    const u1* pEncodedData, Object* classLoader)
{
    ClassObject* newClass = NULL;
    const DexFile* pDexFile;
    const char* descriptor;
    int i;

    pDexFile = pDvmDex->pDexFile;
    descriptor = dexGetClassDescriptor(pDexFile, pClassDef);

    /*
     * Make sure the aren't any "bonus" flags set, since we use them for
     * runtime state.
     */
    if ((pClassDef->accessFlags & ~EXPECTED_FILE_FLAGS) != 0) {
        ALOGW("Invalid file flags in class %s: %04x",
            descriptor, pClassDef->accessFlags);
        return NULL;
    }

    /*
     * Allocate storage for the class object on the GC heap, so that other
     * objects can have references to it.  We bypass the usual mechanism
     * (allocObject), because we don't have all the bits and pieces yet.
     *
     * Note that we assume that java.lang.Class does not override
     * finalize().
     */
    /* TODO: Can there be fewer special checks in the usual path? */
    assert(descriptor != NULL);
    if (classLoader == NULL &&
        strcmp(descriptor, "Ljava/lang/Class;") == 0) {
        assert(gDvm.classJavaLangClass != NULL);
        newClass = gDvm.classJavaLangClass;
    } else {
        size_t size = classObjectSize(pHeader->staticFieldsSize);
        newClass = (ClassObject*) dvmMalloc(size, ALLOC_NON_MOVING);
    }
    if (newClass == NULL)
        return NULL;

    DVM_OBJECT_INIT(newClass, gDvm.classJavaLangClass);
    dvmSetClassSerialNumber(newClass);
    newClass->descriptor = descriptor;
    assert(newClass->descriptorAlloc == NULL);
    SET_CLASS_FLAG(newClass, pClassDef->accessFlags);
    dvmSetFieldObject((Object *)newClass,
                      OFFSETOF_MEMBER(ClassObject, classLoader),
                      (Object *)classLoader);
    newClass->pDvmDex = pDvmDex;
    newClass->primitiveType = PRIM_NOT;
    newClass->status = CLASS_IDX;

    /*
     * Stuff the superclass index into the object pointer field.  The linker
     * pulls it out and replaces it with a resolved ClassObject pointer.
     * I'm doing it this way (rather than having a dedicated superclassIdx
     * field) to save a few bytes of overhead per class.
     *
     * newClass->super is not traversed or freed by dvmFreeClassInnards, so
     * this is safe.
     */
    assert(sizeof(u4) == sizeof(ClassObject*)); /* 32-bit check */
    newClass->super = (ClassObject*) pClassDef->superclassIdx;

    /*
     * Stuff class reference indices into the pointer fields.
     *
     * The elements of newClass->interfaces are not traversed or freed by
     * dvmFreeClassInnards, so this is GC-safe.
     */
    const DexTypeList* pInterfacesList;
    pInterfacesList = dexGetInterfacesList(pDexFile, pClassDef);
    if (pInterfacesList != NULL) {
        newClass->interfaceCount = pInterfacesList->size;
        newClass->interfaces = (ClassObject**) dvmLinearAlloc(classLoader,
                newClass->interfaceCount * sizeof(ClassObject*));

        for (i = 0; i < newClass->interfaceCount; i++) {
            const DexTypeItem* pType = dexGetTypeItem(pInterfacesList, i);
            newClass->interfaces[i] = (ClassObject*)(u4) pType->typeIdx;
        }
        dvmLinearReadOnly(classLoader, newClass->interfaces);
    }

    /* load field definitions */

    /*
     * Over-allocate the class object and append static field info
     * onto the end.  It's fixed-size and known at alloc time.  This
     * seems to increase zygote sharing.  Heap compaction will have to
     * be careful if it ever tries to move ClassObject instances,
     * because we pass Field pointers around internally. But at least
     * now these Field pointers are in the object heap.
     */

    if (pHeader->staticFieldsSize != 0) {
        /* static fields stay on system heap; field data isn't "write once" */
        int count = (int) pHeader->staticFieldsSize;
        u4 lastIndex = 0;
        DexField field;

        newClass->sfieldCount = count;
        for (i = 0; i < count; i++) {
            dexReadClassDataField(&pEncodedData, &field, &lastIndex);
            loadSFieldFromDex(newClass, &field, &newClass->sfields[i]);
        }
    }

    if (pHeader->instanceFieldsSize != 0) {
        int count = (int) pHeader->instanceFieldsSize;
        u4 lastIndex = 0;
        DexField field;

        newClass->ifieldCount = count;
        newClass->ifields = (InstField*) dvmLinearAlloc(classLoader,
                count * sizeof(InstField));
        for (i = 0; i < count; i++) {
            dexReadClassDataField(&pEncodedData, &field, &lastIndex);
            loadIFieldFromDex(newClass, &field, &newClass->ifields[i]);
        }
        dvmLinearReadOnly(classLoader, newClass->ifields);
    }

    /*
     * Load method definitions.  We do this in two batches, direct then
     * virtual.
     *
     * If register maps have already been generated for this class, and
     * precise GC is enabled, we pull out pointers to them.  We know that
     * they were streamed to the DEX file in the same order in which the
     * methods appear.
     *
     * If the class wasn't pre-verified, the maps will be generated when
     * the class is verified during class initialization.
     */
    u4 classDefIdx = dexGetIndexForClassDef(pDexFile, pClassDef);
    const void* classMapData;
    u4 numMethods;

    if (gDvm.preciseGc) {
        classMapData =
            dvmRegisterMapGetClassData(pDexFile, classDefIdx, &numMethods);

        /* sanity check */
        if (classMapData != NULL &&
            pHeader->directMethodsSize + pHeader->virtualMethodsSize != numMethods)
        {
            ALOGE("ERROR: in %s, direct=%d virtual=%d, maps have %d",
                newClass->descriptor, pHeader->directMethodsSize,
                pHeader->virtualMethodsSize, numMethods);
            assert(false);
            classMapData = NULL;        /* abandon */
        }
    } else {
        classMapData = NULL;
    }

    if (pHeader->directMethodsSize != 0) {
        int count = (int) pHeader->directMethodsSize;
        u4 lastIndex = 0;
        DexMethod method;

        newClass->directMethodCount = count;
        newClass->directMethods = (Method*) dvmLinearAlloc(classLoader,
                count * sizeof(Method));
        for (i = 0; i < count; i++) {
            dexReadClassDataMethod(&pEncodedData, &method, &lastIndex);
            loadMethodFromDex(newClass, &method, &newClass->directMethods[i]);
            if (classMapData != NULL) {
                const RegisterMap* pMap = dvmRegisterMapGetNext(&classMapData);
                if (dvmRegisterMapGetFormat(pMap) != kRegMapFormatNone) {
                    newClass->directMethods[i].registerMap = pMap;
                    /* TODO: add rigorous checks */
                    assert((newClass->directMethods[i].registersSize+7) / 8 ==
                        newClass->directMethods[i].registerMap->regWidth);
                }
            }
        }
        dvmLinearReadOnly(classLoader, newClass->directMethods);
    }

    if (pHeader->virtualMethodsSize != 0) {
        int count = (int) pHeader->virtualMethodsSize;
        u4 lastIndex = 0;
        DexMethod method;

        newClass->virtualMethodCount = count;
        newClass->virtualMethods = (Method*) dvmLinearAlloc(classLoader,
                count * sizeof(Method));
        for (i = 0; i < count; i++) {
            dexReadClassDataMethod(&pEncodedData, &method, &lastIndex);
            loadMethodFromDex(newClass, &method, &newClass->virtualMethods[i]);
            if (classMapData != NULL) {
                const RegisterMap* pMap = dvmRegisterMapGetNext(&classMapData);
                if (dvmRegisterMapGetFormat(pMap) != kRegMapFormatNone) {
                    newClass->virtualMethods[i].registerMap = pMap;
                    /* TODO: add rigorous checks */
                    assert((newClass->virtualMethods[i].registersSize+7) / 8 ==
                        newClass->virtualMethods[i].registerMap->regWidth);
                }
            }
        }
        dvmLinearReadOnly(classLoader, newClass->virtualMethods);
    }

    newClass->sourceFile = dexGetSourceFile(pDexFile, pClassDef);

    /* caller must call dvmReleaseTrackedAlloc */
    return newClass;
}

/*
 * Try to load the indicated class from the specified DEX file.
 *
 * This is effectively loadClass()+defineClass() for a DexClassDef.  The
 * loading was largely done when we crunched through the DEX.
 *
 * Returns NULL on failure.  If we locate the class but encounter an error
 * while processing it, an appropriate exception is thrown.
 */
static ClassObject* loadClassFromDex(DvmDex* pDvmDex,
    const DexClassDef* pClassDef, Object* classLoader)
{
    ClassObject* result;
    DexClassDataHeader header;
    const u1* pEncodedData;
    const DexFile* pDexFile;

    assert((pDvmDex != NULL) && (pClassDef != NULL));
    pDexFile = pDvmDex->pDexFile;

    if (gDvm.verboseClass) {
        ALOGV("CLASS: loading '%s'...",
            dexGetClassDescriptor(pDexFile, pClassDef));
    }

    pEncodedData = dexGetClassData(pDexFile, pClassDef);

    if (pEncodedData != NULL) {
        dexReadClassDataHeader(&pEncodedData, &header);
    } else {
        // Provide an all-zeroes header for the rest of the loading.
        memset(&header, 0, sizeof(header));
    }

    result = loadClassFromDex0(pDvmDex, pClassDef, &header, pEncodedData,
            classLoader);

    if (gDvm.verboseClass && (result != NULL)) {
        ALOGI("[Loaded %s from DEX %p (cl=%p)]",
            result->descriptor, pDvmDex, classLoader);
    }

#if defined(WITH_OFFLOAD) || defined(WITH_TRACER)
    result->idx = pClassDef->classIdx;
#endif

    return result;
}

/*
 * Clone a Method, making new copies of anything that will be freed up
 * by freeMethodInnards().  This is used for "miranda" methods.
 */
static void cloneMethod(Method* dst, const Method* src)
{
    if (src->registerMap != NULL) {
        ALOGE("GLITCH: only expected abstract methods here");
        ALOGE("        cloning %s.%s", src->clazz->descriptor, src->name);
        dvmAbort();
    }
    memcpy(dst, src, sizeof(Method));
}

/*
 * Pull the interesting pieces out of a DexMethod.
 *
 * The DEX file isn't going anywhere, so we don't need to make copies of
 * the code area.
 */
static void loadMethodFromDex(ClassObject* clazz, const DexMethod* pDexMethod,
    Method* meth)
{
    DexFile* pDexFile = clazz->pDvmDex->pDexFile;
    const DexMethodId* pMethodId;
    const DexCode* pDexCode;

    pMethodId = dexGetMethodId(pDexFile, pDexMethod->methodIdx);

    meth->name = dexStringById(pDexFile, pMethodId->nameIdx);
    dexProtoSetFromMethodId(&meth->prototype, pDexFile, pMethodId);
    meth->shorty = dexProtoGetShorty(&meth->prototype);
    meth->accessFlags = pDexMethod->accessFlags;
    meth->clazz = clazz;
    meth->jniArgInfo = 0;

#ifdef WITH_OFFLOAD
    if(dvmIsNativeMethod(meth)) {
        offLoadNativeMethod(meth);
    }
#endif

    if (dvmCompareNameDescriptorAndMethod("finalize", "()V", meth) == 0) {
        /*
         * The Enum class declares a "final" finalize() method to
         * prevent subclasses from introducing a finalizer.  We don't
         * want to set the finalizable flag for Enum or its subclasses,
         * so we check for it here.
         *
         * We also want to avoid setting it on Object, but it's easier
         * to just strip that out later.
         */
        if (clazz->classLoader != NULL ||
            strcmp(clazz->descriptor, "Ljava/lang/Enum;") != 0)
        {
            SET_CLASS_FLAG(clazz, CLASS_ISFINALIZABLE);
        }
    }

    pDexCode = dexGetCode(pDexFile, pDexMethod);
    if (pDexCode != NULL) {
        /* integer constants, copy over for faster access */
        meth->registersSize = pDexCode->registersSize;
        meth->insSize = pDexCode->insSize;
        meth->outsSize = pDexCode->outsSize;

        /* pointer to code area */
        meth->insns = pDexCode->insns;
    } else {
        /*
         * We don't have a DexCode block, but we still want to know how
         * much space is needed for the arguments (so we don't have to
         * compute it later).  We also take this opportunity to compute
         * JNI argument info.
         *
         * We do this for abstract methods as well, because we want to
         * be able to substitute our exception-throwing "stub" in.
         */
        int argsSize = dvmComputeMethodArgsSize(meth);
        if (!dvmIsStaticMethod(meth))
            argsSize++;
        meth->registersSize = meth->insSize = argsSize;
        assert(meth->outsSize == 0);
        assert(meth->insns == NULL);

        if (dvmIsNativeMethod(meth)) {
            meth->nativeFunc = dvmResolveNativeMethod;
            meth->jniArgInfo = computeJniArgInfo(&meth->prototype);
        }
    }

#if defined(WITH_OFFLOAD) || defined(WITH_TRACER)
    meth->idx = pDexMethod->methodIdx;
#endif
}

#if 0       /* replaced with private/read-write mapping */
/*
 * We usually map bytecode directly out of the DEX file, which is mapped
 * shared read-only.  If we want to be able to modify it, we have to make
 * a new copy.
 *
 * Once copied, the code will be in the LinearAlloc region, which may be
 * marked read-only.
 *
 * The bytecode instructions are embedded inside a DexCode structure, so we
 * need to copy all of that.  (The dvmGetMethodCode function backs up the
 * instruction pointer to find the start of the DexCode.)
 */
void dvmMakeCodeReadWrite(Method* meth)
{
    DexCode* methodDexCode = (DexCode*) dvmGetMethodCode(meth);

    if (IS_METHOD_FLAG_SET(meth, METHOD_ISWRITABLE)) {
        dvmLinearReadWrite(meth->clazz->classLoader, methodDexCode);
        return;
    }

    assert(!dvmIsNativeMethod(meth) && !dvmIsAbstractMethod(meth));

    size_t dexCodeSize = dexGetDexCodeSize(methodDexCode);
    ALOGD("Making a copy of %s.%s code (%d bytes)",
        meth->clazz->descriptor, meth->name, dexCodeSize);

    DexCode* newCode =
        (DexCode*) dvmLinearAlloc(meth->clazz->classLoader, dexCodeSize);
    memcpy(newCode, methodDexCode, dexCodeSize);

    meth->insns = newCode->insns;
    SET_METHOD_FLAG(meth, METHOD_ISWRITABLE);
}

/*
 * Mark the bytecode read-only.
 *
 * If the contents of the DexCode haven't actually changed, we could revert
 * to the original shared page.
 */
void dvmMakeCodeReadOnly(Method* meth)
{
    DexCode* methodDexCode = (DexCode*) dvmGetMethodCode(meth);
    ALOGV("+++ marking %p read-only", methodDexCode);
    dvmLinearReadOnly(meth->clazz->classLoader, methodDexCode);
}
#endif


/*
 * jniArgInfo (32-bit int) layout:
 *   SRRRHHHH HHHHHHHH HHHHHHHH HHHHHHHH
 *
 *   S - if set, do things the hard way (scan the signature)
 *   R - return-type enumeration
 *   H - target-specific hints
 *
 * This info is used at invocation time by dvmPlatformInvoke.  In most
 * cases, the target-specific hints allow dvmPlatformInvoke to avoid
 * having to fully parse the signature.
 *
 * The return-type bits are always set, even if target-specific hint bits
 * are unavailable.
 */
static int computeJniArgInfo(const DexProto* proto)
{
    const char* sig = dexProtoGetShorty(proto);
    int returnType, jniArgInfo;
    u4 hints;

    /* The first shorty character is the return type. */
    switch (*(sig++)) {
    case 'V':
        returnType = DALVIK_JNI_RETURN_VOID;
        break;
    case 'F':
        returnType = DALVIK_JNI_RETURN_FLOAT;
        break;
    case 'D':
        returnType = DALVIK_JNI_RETURN_DOUBLE;
        break;
    case 'J':
        returnType = DALVIK_JNI_RETURN_S8;
        break;
    case 'Z':
    case 'B':
        returnType = DALVIK_JNI_RETURN_S1;
        break;
    case 'C':
        returnType = DALVIK_JNI_RETURN_U2;
        break;
    case 'S':
        returnType = DALVIK_JNI_RETURN_S2;
        break;
    default:
        returnType = DALVIK_JNI_RETURN_S4;
        break;
    }

    jniArgInfo = returnType << DALVIK_JNI_RETURN_SHIFT;

    hints = dvmPlatformInvokeHints(proto);

    if (hints & DALVIK_JNI_NO_ARG_INFO) {
        jniArgInfo |= DALVIK_JNI_NO_ARG_INFO;
    } else {
        assert((hints & DALVIK_JNI_RETURN_MASK) == 0);
        jniArgInfo |= hints;
    }

    return jniArgInfo;
}

/*
 * Load information about a static field.
 *
 * This also "prepares" static fields by initializing them
 * to their "standard default values".
 */
static void loadSFieldFromDex(ClassObject* clazz,
    const DexField* pDexSField, StaticField* sfield)
{
    DexFile* pDexFile = clazz->pDvmDex->pDexFile;
    const DexFieldId* pFieldId;

    pFieldId = dexGetFieldId(pDexFile, pDexSField->fieldIdx);

    sfield->clazz = clazz;
    sfield->name = dexStringById(pDexFile, pFieldId->nameIdx);
    sfield->signature = dexStringByTypeIdx(pDexFile, pFieldId->typeIdx);
    sfield->accessFlags = pDexSField->accessFlags;

    /* Static object field values are set to "standard default values"
     * (null or 0) until the class is initialized.  We delay loading
     * constant values from the class until that time.
     */
    //sfield->value.j = 0;
    assert(sfield->value.j == 0LL);     // cleared earlier with calloc

#if defined(WITH_OFFLOAD) || defined(WITH_TRACER)
    sfield->idx = pDexSField->fieldIdx;
#endif
}

/*
 * Load information about an instance field.
 */
static void loadIFieldFromDex(ClassObject* clazz,
    const DexField* pDexIField, InstField* ifield)
{
    DexFile* pDexFile = clazz->pDvmDex->pDexFile;
    const DexFieldId* pFieldId;

    pFieldId = dexGetFieldId(pDexFile, pDexIField->fieldIdx);

    ifield->clazz = clazz;
    ifield->name = dexStringById(pDexFile, pFieldId->nameIdx);
    ifield->signature = dexStringByTypeIdx(pDexFile, pFieldId->typeIdx);
    ifield->accessFlags = pDexIField->accessFlags;
#ifndef NDEBUG
    assert(ifield->byteOffset == 0);    // cleared earlier with calloc
    ifield->byteOffset = -1;    // make it obvious if we fail to set later
#endif

#if defined(WITH_OFFLOAD) || defined(WITH_TRACER)
    ifield->idx = pDexIField->fieldIdx;
#endif
}

/*
 * Cache java.lang.ref.Reference fields and methods.
 */
static bool precacheReferenceOffsets(ClassObject* clazz)
{
    int i;

    /* We trick the GC object scanner by not counting
     * java.lang.ref.Reference.referent as an object
     * field.  It will get explicitly scanned as part
     * of the reference-walking process.
     *
     * Find the object field named "referent" and put it
     * just after the list of object reference fields.
     */
    dvmLinearReadWrite(clazz->classLoader, clazz->ifields);
    for (i = 0; i < clazz->ifieldRefCount; i++) {
        InstField *pField = &clazz->ifields[i];
        if (strcmp(pField->name, "referent") == 0) {
            int targetIndex;

            /* Swap this field with the last object field.
             */
            targetIndex = clazz->ifieldRefCount - 1;
            if (i != targetIndex) {
                InstField *swapField = &clazz->ifields[targetIndex];
                InstField tmpField;
                int tmpByteOffset;

                /* It's not currently strictly necessary
                 * for the fields to be in byteOffset order,
                 * but it's more predictable that way.
                 */
                tmpByteOffset = swapField->byteOffset;
                swapField->byteOffset = pField->byteOffset;
                pField->byteOffset = tmpByteOffset;

                tmpField = *swapField;
                *swapField = *pField;
                *pField = tmpField;
            }

            /* One fewer object field (wink wink).
             */
            clazz->ifieldRefCount--;
            i--;        /* don't trip "didn't find it" test if field was last */
            break;
        }
    }
    dvmLinearReadOnly(clazz->classLoader, clazz->ifields);
    if (i == clazz->ifieldRefCount) {
        ALOGE("Unable to reorder 'referent' in %s", clazz->descriptor);
        return false;
    }

    /*
     * Now that the above has been done, it is safe to cache
     * info about the class.
     */
    if (!dvmFindReferenceMembers(clazz)) {
        ALOGE("Trouble with Reference setup");
        return false;
    }

    return true;
}


/*
 * Set the bitmap of reference offsets, refOffsets, from the ifields
 * list.
 */
static void computeRefOffsets(ClassObject* clazz)
{
    if (clazz->super != NULL) {
        clazz->refOffsets = clazz->super->refOffsets;
    } else {
        clazz->refOffsets = 0;
    }
    /*
     * If our superclass overflowed, we don't stand a chance.
     */
    if (clazz->refOffsets != CLASS_WALK_SUPER) {
        InstField *f;
        int i;

        /* All of the fields that contain object references
         * are guaranteed to be at the beginning of the ifields list.
         */
        f = clazz->ifields;
        const int ifieldRefCount = clazz->ifieldRefCount;
        for (i = 0; i < ifieldRefCount; i++) {
          /*
           * Note that, per the comment on struct InstField,
           * f->byteOffset is the offset from the beginning of
           * obj, not the offset into obj->instanceData.
           */
          assert(f->byteOffset >= (int) CLASS_SMALLEST_OFFSET);
          assert((f->byteOffset & (CLASS_OFFSET_ALIGNMENT - 1)) == 0);
          if (CLASS_CAN_ENCODE_OFFSET(f->byteOffset)) {
              u4 newBit = CLASS_BIT_FROM_OFFSET(f->byteOffset);
              assert(newBit != 0);
              clazz->refOffsets |= newBit;
          } else {
              clazz->refOffsets = CLASS_WALK_SUPER;
              break;
          }
          f++;
        }
    }
}


/*
 * Link (prepare and resolve).  Verification is deferred until later.
 *
 * This converts symbolic references into pointers.  It's independent of
 * the source file format.
 *
 * If clazz->status is CLASS_IDX, then clazz->super and interfaces[] are
 * holding class reference indices rather than pointers.  The class
 * references will be resolved during link.  (This is done when
 * loading from DEX to avoid having to create additional storage to
 * pass the indices around.)
 *
 * Returns "false" with an exception pending on failure.
 */
bool customLinkClass(ClassObject* clazz)
{
    u4 superclassIdx = 0;
    u4 *interfaceIdxArray = NULL;
    bool okay = false;
    int i;

    assert(clazz != NULL);
    assert(clazz->descriptor != NULL);
    assert(clazz->status == CLASS_IDX || clazz->status == CLASS_LOADED);
    if (gDvm.verboseClass)
        ALOGV("CLASS: linking '%s'...", clazz->descriptor);

    assert(gDvm.classJavaLangClass != NULL);
    assert(clazz->clazz == gDvm.classJavaLangClass);
    assert(dvmIsClassObject(clazz));
    if (clazz->classLoader == NULL &&
        (strcmp(clazz->descriptor, "Ljava/lang/Class;") == 0))
    {
        if (gDvm.classJavaLangClass->ifieldCount > CLASS_FIELD_SLOTS) {
            ALOGE("java.lang.Class has %d instance fields (expected at most %d)",
                 gDvm.classJavaLangClass->ifieldCount, CLASS_FIELD_SLOTS);
            dvmAbort();
        }
        if (gDvm.classJavaLangClass->sfieldCount != CLASS_SFIELD_SLOTS) {
            ALOGE("java.lang.Class has %d static fields (expected %d)",
                 gDvm.classJavaLangClass->sfieldCount, CLASS_SFIELD_SLOTS);
            dvmAbort();
        }
    }

    /* "Resolve" the class.
     *
     * At this point, clazz's reference fields may contain Dex file
     * indices instead of direct object references.  Proxy objects are
     * an exception, and may be the only exception.  We need to
     * translate those indices into real references, and let the GC
     * look inside this ClassObject.
     */
    if (clazz->status == CLASS_IDX) {
        if (clazz->interfaceCount > 0) {
            /* Copy u4 DEX idx values out of the ClassObject* array
             * where we stashed them.
             */
            assert(sizeof(*interfaceIdxArray) == sizeof(*clazz->interfaces));
            size_t len = clazz->interfaceCount * sizeof(*interfaceIdxArray);
            interfaceIdxArray = (u4*)malloc(len);
            if (interfaceIdxArray == NULL) {
                ALOGW("Unable to allocate memory to link %s", clazz->descriptor);
                goto bail;
            }
            memcpy(interfaceIdxArray, clazz->interfaces, len);

            dvmLinearReadWrite(clazz->classLoader, clazz->interfaces);
            memset(clazz->interfaces, 0, len);
            dvmLinearReadOnly(clazz->classLoader, clazz->interfaces);
        }

        assert(sizeof(superclassIdx) == sizeof(clazz->super));
        superclassIdx = (u4) clazz->super;
        clazz->super = NULL;
        /* After this line, clazz will be fair game for the GC. The
         * superclass and interfaces are all NULL.
         */
        clazz->status = CLASS_LOADED;

        if (superclassIdx != kDexNoIndex) {
            ClassObject* super = dvmResolveClass(clazz, superclassIdx, false);
            if (super == NULL) {
                assert(dvmCheckException(dvmThreadSelf()));
                if (gDvm.optimizing) {
                    /* happens with "external" libs */
                    ALOGV("Unable to resolve superclass of %s (%d)",
                         clazz->descriptor, superclassIdx);
                } else {
                    ALOGW("Unable to resolve superclass of %s (%d)",
                         clazz->descriptor, superclassIdx);
                }
                goto bail;
            }
            dvmSetFieldObject((Object *)clazz,
                              OFFSETOF_MEMBER(ClassObject, super),
                              (Object *)super);
        }

        if (clazz->interfaceCount > 0) {
            /* Resolve the interfaces implemented directly by this class. */
            assert(interfaceIdxArray != NULL);
            dvmLinearReadWrite(clazz->classLoader, clazz->interfaces);
            for (i = 0; i < clazz->interfaceCount; i++) {
                assert(interfaceIdxArray[i] != kDexNoIndex);
                clazz->interfaces[i] =
                    dvmResolveClass(clazz, interfaceIdxArray[i], false);
                if (clazz->interfaces[i] == NULL) {
                    const DexFile* pDexFile = clazz->pDvmDex->pDexFile;

                    assert(dvmCheckException(dvmThreadSelf()));
                    dvmLinearReadOnly(clazz->classLoader, clazz->interfaces);

                    const char* classDescriptor;
                    classDescriptor =
                        dexStringByTypeIdx(pDexFile, interfaceIdxArray[i]);
                    if (gDvm.optimizing) {
                        /* happens with "external" libs */
                        ALOGV("Failed resolving %s interface %d '%s'",
                             clazz->descriptor, interfaceIdxArray[i],
                             classDescriptor);
                    } else {
                        ALOGI("Failed resolving %s interface %d '%s'",
                             clazz->descriptor, interfaceIdxArray[i],
                             classDescriptor);
                    }
                    goto bail;
                }

                /* are we allowed to implement this interface? */
                if (!dvmCheckClassAccess(clazz, clazz->interfaces[i])) {
                    dvmLinearReadOnly(clazz->classLoader, clazz->interfaces);
                    ALOGW("Interface '%s' is not accessible to '%s'",
                         clazz->interfaces[i]->descriptor, clazz->descriptor);
                    dvmThrowIllegalAccessError("interface not accessible");
                    goto bail;
                }
                LOGVV("+++  found interface '%s'",
                      clazz->interfaces[i]->descriptor);
            }
            dvmLinearReadOnly(clazz->classLoader, clazz->interfaces);
        }
    }
    /*
     * There are now Class references visible to the GC in super and
     * interfaces.
     */

    /*
     * All classes have a direct superclass, except for
     * java/lang/Object and primitive classes. Primitive classes are
     * are created CLASS_INITIALIZED, so won't get here.
     */
    assert(clazz->primitiveType == PRIM_NOT);
    if (strcmp(clazz->descriptor, "Ljava/lang/Object;") == 0) {
        if (clazz->super != NULL) {
            /* TODO: is this invariant true for all java/lang/Objects,
             * regardless of the class loader?  For now, assume it is.
             */
            dvmThrowClassFormatError("java.lang.Object has a superclass");
            goto bail;
        }

        /* Don't finalize objects whose classes use the
         * default (empty) Object.finalize().
         */
        CLEAR_CLASS_FLAG(clazz, CLASS_ISFINALIZABLE);
    } else {
        if (clazz->super == NULL) {
            dvmThrowLinkageError("no superclass defined");
            goto bail;
        }
        /* verify */
        if (dvmIsFinalClass(clazz->super)) {
            ALOGW("Superclass of '%s' is final '%s'",
                clazz->descriptor, clazz->super->descriptor);
            dvmThrowIncompatibleClassChangeError("superclass is final");
            goto bail;
        } else if (dvmIsInterfaceClass(clazz->super)) {
            ALOGW("Superclass of '%s' is interface '%s'",
                clazz->descriptor, clazz->super->descriptor);
            dvmThrowIncompatibleClassChangeError("superclass is an interface");
            goto bail;
        } else if (!dvmCheckClassAccess(clazz, clazz->super)) {
            ALOGW("Superclass of '%s' (%s) is not accessible",
                clazz->descriptor, clazz->super->descriptor);
            dvmThrowIllegalAccessError("superclass not accessible");
            goto bail;
        }

        /* Inherit finalizability from the superclass.  If this
         * class also overrides finalize(), its CLASS_ISFINALIZABLE
         * bit will already be set.
         */
        if (IS_CLASS_FLAG_SET(clazz->super, CLASS_ISFINALIZABLE)) {
            SET_CLASS_FLAG(clazz, CLASS_ISFINALIZABLE);
        }

        /* See if this class descends from java.lang.Reference
         * and set the class flags appropriately.
         */
        if (IS_CLASS_FLAG_SET(clazz->super, CLASS_ISREFERENCE)) {
            u4 superRefFlags;

            /* We've already determined the reference type of this
             * inheritance chain.  Inherit reference-ness from the superclass.
             */
            superRefFlags = GET_CLASS_FLAG_GROUP(clazz->super,
                    CLASS_ISREFERENCE |
                    CLASS_ISWEAKREFERENCE |
                    CLASS_ISFINALIZERREFERENCE |
                    CLASS_ISPHANTOMREFERENCE);
            SET_CLASS_FLAG(clazz, superRefFlags);
        } else if (clazz->classLoader == NULL &&
                clazz->super->classLoader == NULL &&
                strcmp(clazz->super->descriptor,
                       "Ljava/lang/ref/Reference;") == 0)
        {
            u4 refFlags;

            /* This class extends Reference, which means it should
             * be one of the magic Soft/Weak/PhantomReference classes.
             */
            refFlags = CLASS_ISREFERENCE;
            if (strcmp(clazz->descriptor,
                       "Ljava/lang/ref/SoftReference;") == 0)
            {
                /* Only CLASS_ISREFERENCE is set for soft references.
                 */
            } else if (strcmp(clazz->descriptor,
                       "Ljava/lang/ref/WeakReference;") == 0)
            {
                refFlags |= CLASS_ISWEAKREFERENCE;
            } else if (strcmp(clazz->descriptor,
                       "Ljava/lang/ref/FinalizerReference;") == 0)
            {
                refFlags |= CLASS_ISFINALIZERREFERENCE;
            }  else if (strcmp(clazz->descriptor,
                       "Ljava/lang/ref/PhantomReference;") == 0)
            {
                refFlags |= CLASS_ISPHANTOMREFERENCE;
            } else {
                /* No-one else is allowed to inherit directly
                 * from Reference.
                 */
//xxx is this the right exception?  better than an assertion.
                dvmThrowLinkageError("illegal inheritance from Reference");
                goto bail;
            }

            /* The class should not have any reference bits set yet.
             */
            assert(GET_CLASS_FLAG_GROUP(clazz,
                    CLASS_ISREFERENCE |
                    CLASS_ISWEAKREFERENCE |
                    CLASS_ISFINALIZERREFERENCE |
                    CLASS_ISPHANTOMREFERENCE) == 0);

            SET_CLASS_FLAG(clazz, refFlags);
        }
    }

    /*
     * Populate vtable.
     */
    if (dvmIsInterfaceClass(clazz)) {
        /* no vtable; just set the method indices */
        int count = clazz->virtualMethodCount;

        if (count != (u2) count) {
            ALOGE("Too many methods (%d) in interface '%s'", count,
                 clazz->descriptor);
            goto bail;
        }

        dvmLinearReadWrite(clazz->classLoader, clazz->virtualMethods);

        for (i = 0; i < count; i++)
            clazz->virtualMethods[i].methodIndex = (u2) i;

        dvmLinearReadOnly(clazz->classLoader, clazz->virtualMethods);
    } else {
        if (!createVtable(clazz)) {
            ALOGW("failed creating vtable");
            goto bail;
        }
    }

    /*
     * Populate interface method tables.  Can alter the vtable.
     */
    if (!createIftable(clazz))
        goto bail;

    /*
     * Insert special-purpose "stub" method implementations.
     */
    if (!insertMethodStubs(clazz))
        goto bail;

    /*
     * Compute instance field offsets and, hence, the size of the object.
     */
    if (!computeFieldOffsets(clazz))
        goto bail;

    /*
     * Cache field and method info for the class Reference (as loaded
     * by the boot classloader). This has to happen after the call to
     * computeFieldOffsets().
     */
    if ((clazz->classLoader == NULL)
            && (strcmp(clazz->descriptor, "Ljava/lang/ref/Reference;") == 0)) {
        if (!precacheReferenceOffsets(clazz)) {
            ALOGE("failed pre-caching Reference offsets");
            dvmThrowInternalError(NULL);
            goto bail;
        }
    }

    /*
     * Compact the offsets the GC has to examine into a bitmap, if
     * possible.  (This has to happen after Reference.referent is
     * massaged in precacheReferenceOffsets.)
     */
    computeRefOffsets(clazz);

    /*
     * Done!
     */
    if (IS_CLASS_FLAG_SET(clazz, CLASS_ISPREVERIFIED))
        clazz->status = CLASS_VERIFIED;
    else
        clazz->status = CLASS_RESOLVED;
    okay = true;
    if (gDvm.verboseClass)
        ALOGV("CLASS: linked '%s'", clazz->descriptor);

    /*
     * We send CLASS_PREPARE events to the debugger from here.  The
     * definition of "preparation" is creating the static fields for a
     * class and initializing them to the standard default values, but not
     * executing any code (that comes later, during "initialization").
     *
     * We did the static prep in loadSFieldFromDex() while loading the class.
     *
     * The class has been prepared and resolved but possibly not yet verified
     * at this point.
     */
    if (gDvm.debuggerActive) {
        dvmDbgPostClassPrepare(clazz);
    }

bail:
    if (!okay) {
        clazz->status = CLASS_ERROR;
        if (!dvmCheckException(dvmThreadSelf())) {
            dvmThrowVirtualMachineError(NULL);
        }
    }
    if (interfaceIdxArray != NULL) {
        free(interfaceIdxArray);
    }

    return okay;
}

/*
 * Create the virtual method table.
 *
 * The top part of the table is a copy of the table from our superclass,
 * with our local methods overriding theirs.  The bottom part of the table
 * has any new methods we defined.
 */
static bool createVtable(ClassObject* clazz)
{
    bool result = false;
    int maxCount;
    int i;

    if (clazz->super != NULL) {
        //ALOGI("SUPER METHODS %d %s->%s", clazz->super->vtableCount,
        //    clazz->descriptor, clazz->super->descriptor);
    }

    /* the virtual methods we define, plus the superclass vtable size */
    maxCount = clazz->virtualMethodCount;
    if (clazz->super != NULL) {
        maxCount += clazz->super->vtableCount;
    } else {
        /* TODO: is this invariant true for all java/lang/Objects,
         * regardless of the class loader?  For now, assume it is.
         */
        assert(strcmp(clazz->descriptor, "Ljava/lang/Object;") == 0);
    }
    //ALOGD("+++ max vmethods for '%s' is %d", clazz->descriptor, maxCount);

    /*
     * Over-allocate the table, then realloc it down if necessary.  So
     * long as we don't allocate anything in between we won't cause
     * fragmentation, and reducing the size should be unlikely to cause
     * a buffer copy.
     */
    dvmLinearReadWrite(clazz->classLoader, clazz->virtualMethods);
    clazz->vtable = (Method**) dvmLinearAlloc(clazz->classLoader,
                        sizeof(Method*) * maxCount);
    if (clazz->vtable == NULL)
        goto bail;

    if (clazz->super != NULL) {
        int actualCount;

        memcpy(clazz->vtable, clazz->super->vtable,
            sizeof(*(clazz->vtable)) * clazz->super->vtableCount);
        actualCount = clazz->super->vtableCount;

        /*
         * See if any of our virtual methods override the superclass.
         */
        for (i = 0; i < clazz->virtualMethodCount; i++) {
            Method* localMeth = &clazz->virtualMethods[i];
            int si;

            for (si = 0; si < clazz->super->vtableCount; si++) {
                Method* superMeth = clazz->vtable[si];

                if (dvmCompareMethodNamesAndProtos(localMeth, superMeth) == 0)
                {
                    /* verify */
                    if (dvmIsFinalMethod(superMeth)) {
                        ALOGW("Method %s.%s overrides final %s.%s",
                            localMeth->clazz->descriptor, localMeth->name,
                            superMeth->clazz->descriptor, superMeth->name);
                        goto bail;
                    }
                    clazz->vtable[si] = localMeth;
                    localMeth->methodIndex = (u2) si;
                    //ALOGV("+++   override %s.%s (slot %d)",
                    //    clazz->descriptor, localMeth->name, si);
                    break;
                }
            }

            if (si == clazz->super->vtableCount) {
                /* not an override, add to end */
                clazz->vtable[actualCount] = localMeth;
                localMeth->methodIndex = (u2) actualCount;
                actualCount++;

                //ALOGV("+++   add method %s.%s",
                //    clazz->descriptor, localMeth->name);
            }
        }

        if (actualCount != (u2) actualCount) {
            ALOGE("Too many methods (%d) in class '%s'", actualCount,
                 clazz->descriptor);
            goto bail;
        }

        assert(actualCount <= maxCount);

        if (actualCount < maxCount) {
            assert(clazz->vtable != NULL);
            dvmLinearReadOnly(clazz->classLoader, clazz->vtable);
            clazz->vtable = (Method **)dvmLinearRealloc(clazz->classLoader,
                clazz->vtable, sizeof(*(clazz->vtable)) * actualCount);
            if (clazz->vtable == NULL) {
                ALOGE("vtable realloc failed");
                goto bail;
            } else {
                LOGVV("+++  reduced vtable from %d to %d",
                    maxCount, actualCount);
            }
        }

        clazz->vtableCount = actualCount;
    } else {
        /* java/lang/Object case */
        int count = clazz->virtualMethodCount;
        if (count != (u2) count) {
            ALOGE("Too many methods (%d) in base class '%s'", count,
                 clazz->descriptor);
            goto bail;
        }

        for (i = 0; i < count; i++) {
            clazz->vtable[i] = &clazz->virtualMethods[i];
            clazz->virtualMethods[i].methodIndex = (u2) i;
        }
        clazz->vtableCount = clazz->virtualMethodCount;
    }

    result = true;

bail:
    dvmLinearReadOnly(clazz->classLoader, clazz->vtable);
    dvmLinearReadOnly(clazz->classLoader, clazz->virtualMethods);
    return result;
}

/*
 * Create and populate "iftable".
 *
 * The set of interfaces we support is the combination of the interfaces
 * we implement directly and those implemented by our superclass.  Each
 * interface can have one or more "superinterfaces", which we must also
 * support.  For speed we flatten the tree out.
 *
 * We might be able to speed this up when there are lots of interfaces
 * by merge-sorting the class pointers and binary-searching when removing
 * duplicates.  We could also drop the duplicate removal -- it's only
 * there to reduce the memory footprint.
 *
 * Because of "Miranda methods", this may reallocate clazz->virtualMethods.
 *
 * Returns "true" on success.
 */
static bool createIftable(ClassObject* clazz)
{
    bool result = false;
    bool zapIftable = false;
    bool zapVtable = false;
    bool zapIfvipool = false;
    int poolOffset = 0, poolSize = 0;
    Method** mirandaList = NULL;
    int mirandaCount = 0, mirandaAlloc = 0;

    int superIfCount;
    if (clazz->super != NULL)
        superIfCount = clazz->super->iftableCount;
    else
        superIfCount = 0;

    int ifCount = superIfCount;
    ifCount += clazz->interfaceCount;
    for (int i = 0; i < clazz->interfaceCount; i++)
        ifCount += clazz->interfaces[i]->iftableCount;

    LOGVV("INTF: class '%s' direct w/supra=%d super=%d total=%d",
        clazz->descriptor, ifCount - superIfCount, superIfCount, ifCount);

    if (ifCount == 0) {
        assert(clazz->iftableCount == 0);
        assert(clazz->iftable == NULL);
        return true;
    }

    /*
     * Create a table with enough space for all interfaces, and copy the
     * superclass' table in.
     */
    clazz->iftable = (InterfaceEntry*) dvmLinearAlloc(clazz->classLoader,
                        sizeof(InterfaceEntry) * ifCount);
    zapIftable = true;
    memset(clazz->iftable, 0x00, sizeof(InterfaceEntry) * ifCount);
    if (superIfCount != 0) {
        memcpy(clazz->iftable, clazz->super->iftable,
            sizeof(InterfaceEntry) * superIfCount);
    }

    /*
     * Create a flattened interface hierarchy of our immediate interfaces.
     */
    int idx = superIfCount;

    for (int i = 0; i < clazz->interfaceCount; i++) {
        ClassObject* interf = clazz->interfaces[i];
        assert(interf != NULL);

        /* make sure this is still an interface class */
        if (!dvmIsInterfaceClass(interf)) {
            ALOGW("Class '%s' implements non-interface '%s'",
                clazz->descriptor, interf->descriptor);
            dvmThrowIncompatibleClassChangeErrorWithClassMessage(
                clazz->descriptor);
            goto bail;
        }

        /* add entry for this interface */
        clazz->iftable[idx++].clazz = interf;

        /* add entries for the interface's superinterfaces */
        for (int j = 0; j < interf->iftableCount; j++) {
            int k;
            ClassObject *cand;

            cand = interf->iftable[j].clazz;

            /*
             * Check if this interface was already added and add only if new.
             * This is to avoid a potential blowup in the number of
             * interfaces for sufficiently complicated interface hierarchies.
             * This has quadratic runtime in the number of interfaces.
             * However, in common cases with little interface inheritance, this
             * doesn't make much of a difference.
             */
            for (k = 0; k < idx; k++)
                if (clazz->iftable[k].clazz == cand)
                    break;

            if (k == idx)
                clazz->iftable[idx++].clazz = cand;
        }
    }

    assert(idx <= ifCount);

    /*
     * Adjust the ifCount. We could reallocate the interface memory here,
     * but it's probably not worth the effort, the important thing here
     * is to avoid the interface blowup and keep the ifCount low.
     */
    if (false) {
        if (idx != ifCount) {
            int newIfCount = idx;
            InterfaceEntry* oldmem = clazz->iftable;

            clazz->iftable = (InterfaceEntry*) dvmLinearAlloc(clazz->classLoader,
                            sizeof(InterfaceEntry) * newIfCount);
            memcpy(clazz->iftable, oldmem, sizeof(InterfaceEntry) * newIfCount);
            dvmLinearFree(clazz->classLoader, oldmem);
        }
    }

    ifCount = idx;
    clazz->iftableCount = ifCount;

    /*
     * If we're an interface, we don't need the vtable pointers, so
     * we're done.  If this class doesn't implement an interface that our
     * superclass doesn't have, then we again have nothing to do.
     */
    if (dvmIsInterfaceClass(clazz) || superIfCount == ifCount) {
        //dvmDumpClass(clazz, kDumpClassFullDetail);
        result = true;
        goto bail;
    }

    /*
     * When we're handling invokeinterface, we probably have an object
     * whose type is an interface class rather than a concrete class.  We
     * need to convert the method reference into a vtable index.  So, for
     * every entry in "iftable", we create a list of vtable indices.
     *
     * Because our vtable encompasses the superclass vtable, we can use
     * the vtable indices from our superclass for all of the interfaces
     * that weren't directly implemented by us.
     *
     * Each entry in "iftable" has a pointer to the start of its set of
     * vtable offsets.  The iftable entries in the superclass point to
     * storage allocated in the superclass, and the iftable entries added
     * for this class point to storage allocated in this class.  "iftable"
     * is flat for fast access in a class and all of its subclasses, but
     * "ifviPool" is only created for the topmost implementor.
     */
    for (int i = superIfCount; i < ifCount; i++) {
        /*
         * Note it's valid for an interface to have no methods (e.g.
         * java/io/Serializable).
         */
        LOGVV("INTF: pool: %d from %s",
            clazz->iftable[i].clazz->virtualMethodCount,
            clazz->iftable[i].clazz->descriptor);
        poolSize += clazz->iftable[i].clazz->virtualMethodCount;
    }

    if (poolSize == 0) {
        LOGVV("INTF: didn't find any new interfaces with methods");
        result = true;
        goto bail;
    }

    clazz->ifviPoolCount = poolSize;
    clazz->ifviPool = (int*) dvmLinearAlloc(clazz->classLoader,
                        poolSize * sizeof(int*));
    zapIfvipool = true;

    /*
     * Fill in the vtable offsets for the interfaces that weren't part of
     * our superclass.
     */
    for (int i = superIfCount; i < ifCount; i++) {
        ClassObject* interface;
        int methIdx;

        clazz->iftable[i].methodIndexArray = clazz->ifviPool + poolOffset;
        interface = clazz->iftable[i].clazz;
        poolOffset += interface->virtualMethodCount;    // end here

        /*
         * For each method listed in the interface's method list, find the
         * matching method in our class's method list.  We want to favor the
         * subclass over the superclass, which just requires walking
         * back from the end of the vtable.  (This only matters if the
         * superclass defines a private method and this class redefines
         * it -- otherwise it would use the same vtable slot.  In Dalvik
         * those don't end up in the virtual method table, so it shouldn't
         * matter which direction we go.  We walk it backward anyway.)
         *
         *
         * Suppose we have the following arrangement:
         *   public interface MyInterface
         *     public boolean inInterface();
         *   public abstract class MirandaAbstract implements MirandaInterface
         *     //public abstract boolean inInterface(); // not declared!
         *     public boolean inAbstract() { stuff }    // in vtable
         *   public class MirandClass extends MirandaAbstract
         *     public boolean inInterface() { stuff }
         *     public boolean inAbstract() { stuff }    // in vtable
         *
         * The javac compiler happily compiles MirandaAbstract even though
         * it doesn't declare all methods from its interface.  When we try
         * to set up a vtable for MirandaAbstract, we find that we don't
         * have an slot for inInterface.  To prevent this, we synthesize
         * abstract method declarations in MirandaAbstract.
         *
         * We have to expand vtable and update some things that point at it,
         * so we accumulate the method list and do it all at once below.
         */
        for (methIdx = 0; methIdx < interface->virtualMethodCount; methIdx++) {
            Method* imeth = &interface->virtualMethods[methIdx];
            int j;

            IF_LOGVV() {
                char* desc = dexProtoCopyMethodDescriptor(&imeth->prototype);
                LOGVV("INTF:  matching '%s' '%s'", imeth->name, desc);
                free(desc);
            }

            for (j = clazz->vtableCount-1; j >= 0; j--) {
                if (dvmCompareMethodNamesAndProtos(imeth, clazz->vtable[j])
                    == 0)
                {
                    LOGVV("INTF:   matched at %d", j);
                    if (!dvmIsPublicMethod(clazz->vtable[j])) {
                        ALOGW("Implementation of %s.%s is not public",
                            clazz->descriptor, clazz->vtable[j]->name);
                        dvmThrowIllegalAccessError(
                            "interface implementation not public");
                        goto bail;
                    }
                    clazz->iftable[i].methodIndexArray[methIdx] = j;
                    break;
                }
            }
            if (j < 0) {
                IF_ALOGV() {
                    char* desc =
                        dexProtoCopyMethodDescriptor(&imeth->prototype);
                    ALOGV("No match for '%s' '%s' in '%s' (creating miranda)",
                            imeth->name, desc, clazz->descriptor);
                    free(desc);
                }
                //dvmThrowRuntimeException("Miranda!");
                //return false;

                if (mirandaCount == mirandaAlloc) {
                    mirandaAlloc += 8;
                    if (mirandaList == NULL) {
                        mirandaList = (Method**)dvmLinearAlloc(
                                        clazz->classLoader,
                                        mirandaAlloc * sizeof(Method*));
                    } else {
                        dvmLinearReadOnly(clazz->classLoader, mirandaList);
                        mirandaList = (Method**)dvmLinearRealloc(
                                clazz->classLoader,
                                mirandaList, mirandaAlloc * sizeof(Method*));
                    }
                    assert(mirandaList != NULL);    // mem failed + we leaked
                }

                /*
                 * These may be redundant (e.g. method with same name and
                 * signature declared in two interfaces implemented by the
                 * same abstract class).  We can squeeze the duplicates
                 * out here.
                 */
                int mir;
                for (mir = 0; mir < mirandaCount; mir++) {
                    if (dvmCompareMethodNamesAndProtos(
                            mirandaList[mir], imeth) == 0)
                    {
                        IF_LOGVV() {
                            char* desc = dexProtoCopyMethodDescriptor(
                                    &imeth->prototype);
                            LOGVV("MIRANDA dupe: %s and %s %s%s",
                                mirandaList[mir]->clazz->descriptor,
                                imeth->clazz->descriptor,
                                imeth->name, desc);
                            free(desc);
                        }
                        break;
                    }
                }

                /* point the iftable at a phantom slot index */
                clazz->iftable[i].methodIndexArray[methIdx] =
                    clazz->vtableCount + mir;
                LOGVV("MIRANDA: %s points at slot %d",
                    imeth->name, clazz->vtableCount + mir);

                /* if non-duplicate among Mirandas, add to Miranda list */
                if (mir == mirandaCount) {
                    //ALOGV("MIRANDA: holding '%s' in slot %d",
                    //    imeth->name, mir);
                    mirandaList[mirandaCount++] = imeth;
                }
            }
        }
    }

    if (mirandaCount != 0) {
        static const int kManyMirandas = 150;   /* arbitrary */
        Method* newVirtualMethods;
        Method* meth;
        int oldMethodCount, oldVtableCount;

        for (int i = 0; i < mirandaCount; i++) {
            LOGVV("MIRANDA %d: %s.%s", i,
                mirandaList[i]->clazz->descriptor, mirandaList[i]->name);
        }
        if (mirandaCount > kManyMirandas) {
            /*
             * Some obfuscators like to create an interface with a huge
             * pile of methods, declare classes as implementing it, and then
             * only define a couple of methods.  This leads to a rather
             * massive collection of Miranda methods and a lot of wasted
             * space, sometimes enough to blow out the LinearAlloc cap.
             */
            ALOGD("Note: class %s has %d unimplemented (abstract) methods",
                clazz->descriptor, mirandaCount);
        }

        /*
         * We found methods in one or more interfaces for which we do not
         * have vtable entries.  We have to expand our virtualMethods
         * table (which might be empty) to hold some new entries.
         */
        if (clazz->virtualMethods == NULL) {
            newVirtualMethods = (Method*) dvmLinearAlloc(clazz->classLoader,
                sizeof(Method) * (clazz->virtualMethodCount + mirandaCount));
        } else {
            //dvmLinearReadOnly(clazz->classLoader, clazz->virtualMethods);
            newVirtualMethods = (Method*) dvmLinearRealloc(clazz->classLoader,
                clazz->virtualMethods,
                sizeof(Method) * (clazz->virtualMethodCount + mirandaCount));
        }
        if (newVirtualMethods != clazz->virtualMethods) {
            /*
             * Table was moved in memory.  We have to run through the
             * vtable and fix the pointers.  The vtable entries might be
             * pointing at superclasses, so we flip it around: run through
             * all locally-defined virtual methods, and fix their entries
             * in the vtable.  (This would get really messy if sub-classes
             * had already been loaded.)
             *
             * Reminder: clazz->virtualMethods and clazz->virtualMethodCount
             * hold the virtual methods declared by this class.  The
             * method's methodIndex is the vtable index, and is the same
             * for all sub-classes (and all super classes in which it is
             * defined).  We're messing with these because the Miranda
             * stuff makes it look like the class actually has an abstract
             * method declaration in it.
             */
            LOGVV("MIRANDA fixing vtable pointers");
            dvmLinearReadWrite(clazz->classLoader, clazz->vtable);
            Method* meth = newVirtualMethods;
            for (int i = 0; i < clazz->virtualMethodCount; i++, meth++)
                clazz->vtable[meth->methodIndex] = meth;
            dvmLinearReadOnly(clazz->classLoader, clazz->vtable);
        }

        oldMethodCount = clazz->virtualMethodCount;
        clazz->virtualMethods = newVirtualMethods;
        clazz->virtualMethodCount += mirandaCount;

        dvmLinearReadOnly(clazz->classLoader, clazz->virtualMethods);

        /*
         * We also have to expand the vtable.
         */
        assert(clazz->vtable != NULL);
        clazz->vtable = (Method**) dvmLinearRealloc(clazz->classLoader,
                        clazz->vtable,
                        sizeof(Method*) * (clazz->vtableCount + mirandaCount));
        if (clazz->vtable == NULL) {
            assert(false);
            goto bail;
        }
        zapVtable = true;

        oldVtableCount = clazz->vtableCount;
        clazz->vtableCount += mirandaCount;

        /*
         * Now we need to create the fake methods.  We clone the abstract
         * method definition from the interface and then replace a few
         * things.
         *
         * The Method will be an "abstract native", with nativeFunc set to
         * dvmAbstractMethodStub().
         */
        meth = clazz->virtualMethods + oldMethodCount;
        for (int i = 0; i < mirandaCount; i++, meth++) {
            dvmLinearReadWrite(clazz->classLoader, clazz->virtualMethods);
            cloneMethod(meth, mirandaList[i]);
            meth->clazz = clazz;
            meth->accessFlags |= ACC_MIRANDA;
            meth->methodIndex = (u2) (oldVtableCount + i);
            dvmLinearReadOnly(clazz->classLoader, clazz->virtualMethods);

            /* point the new vtable entry at the new method */
            clazz->vtable[oldVtableCount + i] = meth;
        }

        dvmLinearReadOnly(clazz->classLoader, mirandaList);
        dvmLinearFree(clazz->classLoader, mirandaList);

    }

    /*
     * TODO?
     * Sort the interfaces by number of declared methods.  All we really
     * want is to get the interfaces with zero methods at the end of the
     * list, so that when we walk through the list during invoke-interface
     * we don't examine interfaces that can't possibly be useful.
     *
     * The set will usually be small, so a simple insertion sort works.
     *
     * We have to be careful not to change the order of two interfaces
     * that define the same method.  (Not a problem if we only move the
     * zero-method interfaces to the end.)
     *
     * PROBLEM:
     * If we do this, we will no longer be able to identify super vs.
     * current class interfaces by comparing clazz->super->iftableCount.  This
     * breaks anything that only wants to find interfaces declared directly
     * by the class (dvmFindStaticFieldHier, ReferenceType.Interfaces,
     * dvmDbgOutputAllInterfaces, etc).  Need to provide a workaround.
     *
     * We can sort just the interfaces implemented directly by this class,
     * but that doesn't seem like it would provide much of an advantage.  I'm
     * not sure this is worthwhile.
     *
     * (This has been made largely obsolete by the interface cache mechanism.)
     */

    //dvmDumpClass(clazz);

    result = true;

bail:
    if (zapIftable)
        dvmLinearReadOnly(clazz->classLoader, clazz->iftable);
    if (zapVtable)
        dvmLinearReadOnly(clazz->classLoader, clazz->vtable);
    if (zapIfvipool)
        dvmLinearReadOnly(clazz->classLoader, clazz->ifviPool);
    return result;
}


/*
 * Provide "stub" implementations for methods without them.
 *
 * Currently we provide an implementation for all abstract methods that
 * throws an AbstractMethodError exception.  This allows us to avoid an
 * explicit check for abstract methods in every virtual call.
 *
 * NOTE: for Miranda methods, the method declaration is a clone of what
 * was found in the interface class.  That copy may already have had the
 * function pointer filled in, so don't be surprised if it's not NULL.
 *
 * NOTE: this sets the "native" flag, giving us an "abstract native" method,
 * which is nonsensical.  Need to make sure that this doesn't escape the
 * VM.  We can either mask it out in reflection calls, or copy "native"
 * into the high 16 bits of accessFlags and check that internally.
 */
static bool insertMethodStubs(ClassObject* clazz)
{
    dvmLinearReadWrite(clazz->classLoader, clazz->virtualMethods);

    Method* meth;
    int i;

    meth = clazz->virtualMethods;
    for (i = 0; i < clazz->virtualMethodCount; i++, meth++) {
        if (dvmIsAbstractMethod(meth)) {
            assert(meth->insns == NULL);
            assert(meth->nativeFunc == NULL ||
                meth->nativeFunc == (DalvikBridgeFunc)dvmAbstractMethodStub);

            meth->accessFlags |= ACC_NATIVE;
            meth->nativeFunc = (DalvikBridgeFunc) dvmAbstractMethodStub;
        }
    }

    dvmLinearReadOnly(clazz->classLoader, clazz->virtualMethods);
    return true;
}


/*
 * Swap two instance fields.
 */
static inline void swapField(InstField* pOne, InstField* pTwo)
{
    InstField swap;

    LOGVV("  --- swap '%s' and '%s'", pOne->name, pTwo->name);
    swap = *pOne;
    *pOne = *pTwo;
    *pTwo = swap;
}

/*
 * Assign instance fields to u4 slots.
 *
 * The top portion of the instance field area is occupied by the superclass
 * fields, the bottom by the fields for this class.
 *
 * "long" and "double" fields occupy two adjacent slots.  On some
 * architectures, 64-bit quantities must be 64-bit aligned, so we need to
 * arrange fields (or introduce padding) to ensure this.  We assume the
 * fields of the topmost superclass (i.e. Object) are 64-bit aligned, so
 * we can just ensure that the offset is "even".  To avoid wasting space,
 * we want to move non-reference 32-bit fields into gaps rather than
 * creating pad words.
 *
 * In the worst case we will waste 4 bytes, but because objects are
 * allocated on >= 64-bit boundaries, those bytes may well be wasted anyway
 * (assuming this is the most-derived class).
 *
 * Pad words are not represented in the field table, so the field table
 * itself does not change size.
 *
 * The number of field slots determines the size of the object, so we
 * set that here too.
 *
 * This function feels a little more complicated than I'd like, but it
 * has the property of moving the smallest possible set of fields, which
 * should reduce the time required to load a class.
 *
 * NOTE: reference fields *must* come first, or precacheReferenceOffsets()
 * will break.
 */
static bool computeFieldOffsets(ClassObject* clazz)
{
    int fieldOffset;
    int i, j;

    dvmLinearReadWrite(clazz->classLoader, clazz->ifields);

    if (clazz->super != NULL)
        fieldOffset = clazz->super->objectSize;
    else
        fieldOffset = OFFSETOF_MEMBER(DataObject, instanceData);

    LOGVV("--- computeFieldOffsets '%s'", clazz->descriptor);

    //ALOGI("OFFSETS fieldCount=%d", clazz->ifieldCount);
    //ALOGI("dataobj, instance: %d", offsetof(DataObject, instanceData));
    //ALOGI("classobj, access: %d", offsetof(ClassObject, accessFlags));
    //ALOGI("super=%p, fieldOffset=%d", clazz->super, fieldOffset);

    /*
     * Start by moving all reference fields to the front.
     */
    clazz->ifieldRefCount = 0;
    j = clazz->ifieldCount - 1;
    for (i = 0; i < clazz->ifieldCount; i++) {
        InstField* pField = &clazz->ifields[i];
        char c = pField->signature[0];

        if (c != '[' && c != 'L') {
            /* This isn't a reference field; see if any reference fields
             * follow this one.  If so, we'll move it to this position.
             * (quicksort-style partitioning)
             */
            while (j > i) {
                InstField* refField = &clazz->ifields[j--];
                char rc = refField->signature[0];

                if (rc == '[' || rc == 'L') {
                    /* Here's a reference field that follows at least one
                     * non-reference field.  Swap it with the current field.
                     * (When this returns, "pField" points to the reference
                     * field, and "refField" points to the non-ref field.)
                     */
                    swapField(pField, refField);

                    /* Fix the signature.
                     */
                    c = rc;

                    clazz->ifieldRefCount++;
                    break;
                }
            }
            /* We may or may not have swapped a field.
             */
        } else {
            /* This is a reference field.
             */
            clazz->ifieldRefCount++;
        }

        /*
         * If we've hit the end of the reference fields, break.
         */
        if (c != '[' && c != 'L')
            break;

        pField->byteOffset = fieldOffset;
        fieldOffset += sizeof(u4);
        LOGVV("  --- offset1 '%s'=%d", pField->name,pField->byteOffset);
    }

    /*
     * Now we want to pack all of the double-wide fields together.  If we're
     * not aligned, though, we want to shuffle one 32-bit field into place.
     * If we can't find one, we'll have to pad it.
     */
    if (i != clazz->ifieldCount && (fieldOffset & 0x04) != 0) {
        LOGVV("  +++ not aligned");

        InstField* pField = &clazz->ifields[i];
        char c = pField->signature[0];

        if (c != 'J' && c != 'D') {
            /*
             * The field that comes next is 32-bit, so just advance past it.
             */
            assert(c != '[' && c != 'L');
            pField->byteOffset = fieldOffset;
            fieldOffset += sizeof(u4);
            i++;
            LOGVV("  --- offset2 '%s'=%d",
                pField->name, pField->byteOffset);
        } else {
            /*
             * Next field is 64-bit, so search for a 32-bit field we can
             * swap into it.
             */
            bool found = false;
            j = clazz->ifieldCount - 1;
            while (j > i) {
                InstField* singleField = &clazz->ifields[j--];
                char rc = singleField->signature[0];

                if (rc != 'J' && rc != 'D') {
                    swapField(pField, singleField);
                    //c = rc;
                    LOGVV("  +++ swapped '%s' for alignment",
                        pField->name);
                    pField->byteOffset = fieldOffset;
                    fieldOffset += sizeof(u4);
                    LOGVV("  --- offset3 '%s'=%d",
                        pField->name, pField->byteOffset);
                    found = true;
                    i++;
                    break;
                }
            }
            if (!found) {
                ALOGV("  +++ inserting pad field in '%s'", clazz->descriptor);
                fieldOffset += sizeof(u4);
            }
        }
    }

    /*
     * Alignment is good, shuffle any double-wide fields forward, and
     * finish assigning field offsets to all fields.
     */
    assert(i == clazz->ifieldCount || (fieldOffset & 0x04) == 0);
    j = clazz->ifieldCount - 1;
    for ( ; i < clazz->ifieldCount; i++) {
        InstField* pField = &clazz->ifields[i];
        char c = pField->signature[0];

        if (c != 'D' && c != 'J') {
            /* This isn't a double-wide field; see if any double fields
             * follow this one.  If so, we'll move it to this position.
             * (quicksort-style partitioning)
             */
            while (j > i) {
                InstField* doubleField = &clazz->ifields[j--];
                char rc = doubleField->signature[0];

                if (rc == 'D' || rc == 'J') {
                    /* Here's a double-wide field that follows at least one
                     * non-double field.  Swap it with the current field.
                     * (When this returns, "pField" points to the reference
                     * field, and "doubleField" points to the non-double field.)
                     */
                    swapField(pField, doubleField);
                    c = rc;

                    break;
                }
            }
            /* We may or may not have swapped a field.
             */
        } else {
            /* This is a double-wide field, leave it be.
             */
        }

        pField->byteOffset = fieldOffset;
        LOGVV("  --- offset4 '%s'=%d", pField->name,pField->byteOffset);
        fieldOffset += sizeof(u4);
        if (c == 'J' || c == 'D')
            fieldOffset += sizeof(u4);
    }

#ifndef NDEBUG
    /* Make sure that all reference fields appear before
     * non-reference fields, and all double-wide fields are aligned.
     */
    j = 0;  // seen non-ref
    for (i = 0; i < clazz->ifieldCount; i++) {
        InstField *pField = &clazz->ifields[i];
        char c = pField->signature[0];

        if (c == 'D' || c == 'J') {
            assert((pField->byteOffset & 0x07) == 0);
        }

        if (c != '[' && c != 'L') {
            if (!j) {
                assert(i == clazz->ifieldRefCount);
                j = 1;
            }
        } else if (j) {
            assert(false);
        }
    }
    if (!j) {
        assert(clazz->ifieldRefCount == clazz->ifieldCount);
    }
#endif

    /*
     * We map a C struct directly on top of java/lang/Class objects.  Make
     * sure we left enough room for the instance fields.
     */
    assert(!dvmIsTheClassClass(clazz) || (size_t)fieldOffset <
        OFFSETOF_MEMBER(ClassObject, instanceData) + sizeof(clazz->instanceData));

    clazz->objectSize = fieldOffset;

    dvmLinearReadOnly(clazz->classLoader, clazz->ifields);
    return true;
}

/*
 * The class failed to initialize on a previous attempt, so we want to throw
 * a NoClassDefFoundError (v2 2.17.5).  The exception to this rule is if we
 * failed in verification, in which case v2 5.4.1 says we need to re-throw
 * the previous error.
 */
static void throwEarlierClassFailure(ClassObject* clazz)
{
    ALOGI("Rejecting re-init on previously-failed class %s v=%p",
        clazz->descriptor, clazz->verifyErrorClass);

    if (clazz->verifyErrorClass == NULL) {
        dvmThrowNoClassDefFoundError(clazz->descriptor);
    } else {
        dvmThrowExceptionWithClassMessage(clazz->verifyErrorClass,
            clazz->descriptor);
    }
}


/*
 * Determine whether "descriptor" yields the same class object in the
 * context of clazz1 and clazz2.
 *
 * The caller must hold gDvm.loadedClasses.
 *
 * Returns "true" if they match.
 */
static bool compareDescriptorClasses(const char* descriptor,
    const ClassObject* clazz1, const ClassObject* clazz2)
{
    ClassObject* result1;
    ClassObject* result2;

    /*
     * Do the first lookup by name.
     */
    result1 = dvmFindClassNoInit(descriptor, clazz1->classLoader);

    /*
     * We can skip a second lookup by name if the second class loader is
     * in the initiating loader list of the class object we retrieved.
     * (This means that somebody already did a lookup of this class through
     * the second loader, and it resolved to the same class.)  If it's not
     * there, we may simply not have had an opportunity to add it yet, so
     * we do the full lookup.
     *
     * The initiating loader test should catch the majority of cases
     * (in particular, the zillions of references to String/Object).
     *
     * Unfortunately we're still stuck grabbing a mutex to do the lookup.
     *
     * For this to work, the superclass/interface should be the first
     * argument, so that way if it's from the bootstrap loader this test
     * will work.  (The bootstrap loader, by definition, never shows up
     * as the initiating loader of a class defined by some other loader.)
     */
    dvmHashTableLock(gDvm.loadedClasses);
    bool isInit = dvmLoaderInInitiatingList(result1, clazz2->classLoader);
    dvmHashTableUnlock(gDvm.loadedClasses);

    if (isInit) {
        //printf("%s(obj=%p) / %s(cl=%p): initiating\n",
        //    result1->descriptor, result1,
        //    clazz2->descriptor, clazz2->classLoader);
        return true;
    } else {
        //printf("%s(obj=%p) / %s(cl=%p): RAW\n",
        //    result1->descriptor, result1,
        //    clazz2->descriptor, clazz2->classLoader);
        result2 = dvmFindClassNoInit(descriptor, clazz2->classLoader);
    }

    if (result1 == NULL || result2 == NULL) {
        dvmClearException(dvmThreadSelf());
        if (result1 == result2) {
            /*
             * Neither class loader could find this class.  Apparently it
             * doesn't exist.
             *
             * We can either throw some sort of exception now, or just
             * assume that it'll fail later when something actually tries
             * to use the class.  For strict handling we should throw now,
             * because a "tricky" class loader could start returning
             * something later, and a pair of "tricky" loaders could set
             * us up for confusion.
             *
             * I'm not sure if we're allowed to complain about nonexistent
             * classes in method signatures during class init, so for now
             * this will just return "true" and let nature take its course.
             */
            return true;
        } else {
            /* only one was found, so clearly they're not the same */
            return false;
        }
    }

    return result1 == result2;
}

/*
 * For every component in the method descriptor, resolve the class in the
 * context of the two classes and compare the results.
 *
 * For best results, the "superclass" class should be first.
 *
 * Returns "true" if the classes match, "false" otherwise.
 */
static bool checkMethodDescriptorClasses(const Method* meth,
    const ClassObject* clazz1, const ClassObject* clazz2)
{
    DexParameterIterator iterator;
    const char* descriptor;

    /* walk through the list of parameters */
    dexParameterIteratorInit(&iterator, &meth->prototype);
    while (true) {
        descriptor = dexParameterIteratorNextDescriptor(&iterator);

        if (descriptor == NULL)
            break;

        if (descriptor[0] == 'L' || descriptor[0] == '[') {
            /* non-primitive type */
            if (!compareDescriptorClasses(descriptor, clazz1, clazz2))
                return false;
        }
    }

    /* check the return type */
    descriptor = dexProtoGetReturnType(&meth->prototype);
    if (descriptor[0] == 'L' || descriptor[0] == '[') {
        if (!compareDescriptorClasses(descriptor, clazz1, clazz2))
            return false;
    }
    return true;
}

