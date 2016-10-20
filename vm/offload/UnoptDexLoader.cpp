
#include "Dalvik.h"
#include "ParserCommon.h"
#include "CustomizedClass.h"
#define LOG_CLASS_LOADING 0

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
#include <string>

#include <libgen.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/file.h>
#include <sys/types.h>
#include <fcntl.h>
#include <errno.h>
#include <unistd.h>
#include <zlib.h>
#include <time.h>

static const char* kDexInJarName = "classes.dex";
ClassObject* javaLangObject;
std::set<ClassObject*>* exemptClzs = new std::set<ClassObject*>();
std::set<ClassObject*>* exemptIfs = new std::set<ClassObject*>();
extern std::vector<DvmDex*> loadedDex;
extern char* basePath;
extern unsigned int MaxSubCount;

/*
 * Open a Jar file.  But we do not try to optimize the dex.
 *
 * If "isBootstrap" is not set, the optimizer/verifier regards this DEX as
 * being part of a different class loader.
 */
int jarFileOpen(const char* fileName, const char* dexOutputName,
    JarFile** ppJarFile, bool isBootstrap)
{
    /*
     * TODO: This function has been duplicated and modified to become
     * dvmRawDexFileOpen() in RawDexFile.c. This should be refactored.
     */

    ZipArchive archive;
    DvmDex* pDvmDex = NULL;
    char* cachedName = NULL;
    bool archiveOpen = false;
    int fd = -1;
    int result = -1;

    /* Even if we're not going to look at the archive, we need to
     * open it so we can stuff it into ppJarFile.
     */
    if (dexZipOpenArchive(fileName, &archive) != 0)
        goto bail;
    archiveOpen = true;

    /* If we fork/exec into dexopt, don't let it inherit the archive's fd.
     */
    dvmSetCloseOnExec(dexZipGetArchiveFd(&archive));
    ZipEntry entry;

    /*
     * Look inside the jar for a "classes.dex".
     */
    entry = dexZipFindEntry(&archive, kDexInJarName);
    if (entry != NULL) {
        cachedName = strdup(dexOutputName);
        ALOGV("dvmJarFileOpen: Checking cache for %s (%s)", fileName, cachedName);
        fd = open(cachedName, O_CREAT|O_RDWR|O_TRUNC, 0777);
        if (fd < 0) {
            ALOGI("Unable to open or create cache for %s (%s)", fileName, cachedName);
            goto bail;
        }
        dexZipExtractEntryToFile(&archive, entry, fd);
    } else {
        ALOGI("Zip is good, but no %s inside", kDexInJarName);
        goto bail;
    }

    /*
     * Map the cached version.  This immediately rewinds the fd, so it
     * doesn't have to be seeked anywhere in particular.
     */
    if (dvmDexFileOpenFromFd(fd, &pDvmDex) != 0) {
        ALOGI("Unable to map %s in %s", kDexInJarName, fileName);
        goto bail;
    }

    ALOGV("Successfully opened '%s' in '%s'", kDexInJarName, fileName);

    *ppJarFile = (JarFile*) calloc(1, sizeof(JarFile));
    (*ppJarFile)->archive = archive;
    (*ppJarFile)->cacheFileName = cachedName;
    (*ppJarFile)->pDvmDex = pDvmDex;
    cachedName = NULL;      // don't free it below
    result = 0;

bail:
    /* clean up, closing the open file */
    if (archiveOpen && result != 0)
        dexZipCloseArchive(&archive);
    free(cachedName);
    if (fd >= 0) {
        close(fd);
    }
    return result;
}


/*
 * Get the filename suffix of the given file (everything after the
 * last "." if any, or "<none>" if there's no apparent suffix). The
 * passed-in buffer will always be '\0' terminated.
 */
static void getFileNameSuffix(const char* fileName, char* suffixBuf, size_t suffixBufLen)
{
    const char* lastDot = strrchr(fileName, '.');

    strlcpy(suffixBuf, (lastDot == NULL) ? "<none>" : (lastDot + 1), suffixBufLen);
}
static void getFileActualName(const char* fileName, char* nameBuf, size_t nameBufLen)
{
    const char* lastSlash = strrchr(fileName, '/');
    const char* lastDot = strrchr(fileName, '.');
    size_t len;
    if(lastDot != NULL && lastSlash != NULL) {
        len = lastDot - lastSlash;
    } else {
        len = nameBufLen;
    }
    if(len > nameBufLen) {
        len = nameBufLen;
    }

    strlcpy(nameBuf, (lastSlash == NULL) ? fileName : (lastSlash + 1), len);
}
/*
 * Prepare a ClassPathEntry struct, which at this point only has a valid
 * filename.  We need to figure out what kind of file it is, and for
 * everything other than directories we need to open it up and see
 * what's inside.
 */
static bool prepareCpe(ClassPathEntry* cpe, bool isBootstrap)
{
    struct stat sb;

    if (stat(cpe->fileName, &sb) < 0) {
        //ALOGD("Unable to stat classpath element '%s'", cpe->fileName);
        return false;
    }
    if (S_ISDIR(sb.st_mode)) {
        //ALOGE("Directory classpath elements are not supported: %s", cpe->fileName);
        return false;
    }

    char suffix[10];
    getFileNameSuffix(cpe->fileName, suffix, sizeof(suffix));
    char name[20];
    //ALOGE("the name is: %s", name);
    getFileActualName(cpe->fileName, name, sizeof(name));
    char newname[80];
    strcpy(newname, "/home/yli118/apkanalysis/");
    strcat(newname, name);
    strcat(newname, ".class.dex");

    if ((strcmp(suffix, "jar") == 0) || (strcmp(suffix, "zip") == 0) ||
            (strcmp(suffix, "apk") == 0)) {
        JarFile* pJarFile = NULL;
        if (jarFileOpen(cpe->fileName, newname, &pJarFile, isBootstrap) == 0) {
            cpe->kind = kCpeJar;
            cpe->ptr = pJarFile;
            return true;
        }
    } else if (strcmp(suffix, "dex") == 0) {
        RawDexFile* pRawDexFile = NULL;
        if (dvmRawDexFileOpen(cpe->fileName, NULL, &pRawDexFile, isBootstrap) == 0) {
            cpe->kind = kCpeDex;
            cpe->ptr = pRawDexFile;
            return true;
        }
    } else {
        //ALOGE("Unknown type suffix '%s'", suffix);
    }

    ALOGD("Unable to process classpath element '%s'", cpe->fileName);
    return false;
}
ClassPathEntry* processClassPath(const char* pathStr)
{
    ClassPathEntry* cpe = NULL;
    char* mangle;
    char* cp;
    const char* end;
    int idx, count;

    assert(pathStr != NULL);

    mangle = strdup(pathStr);

    /*
     * Run through and essentially strtok() the string.  Get a count of
     * the #of elements while we're at it.
     *
     * If the path was constructed strangely (e.g. ":foo::bar:") this will
     * over-allocate, which isn't ideal but is mostly harmless.
     */
    count = 1;
    for (cp = mangle; *cp != '\0'; cp++) {
        if (*cp == ':') {   /* separates two entries */
            count++;
            *cp = '\0';
        }
    }
    end = cp;

    /*
     * Allocate storage.  We over-alloc by one so we can set an "end" marker.
     */
    cpe = (ClassPathEntry*) calloc(count+1, sizeof(ClassPathEntry));

    /*
     * Set the global pointer so the DEX file dependency stuff can find it.
     */
    gDvm.bootClassPath = cpe;

    /*
     * Go through a second time, pulling stuff out.
     */
    cp = mangle;
    idx = 0;
    while (cp < end) {
        if (*cp == '\0') {
            /* leading, trailing, or doubled ':'; ignore it */
        } else {

            ClassPathEntry tmp;
            tmp.kind = kCpeUnknown;
            tmp.fileName = strdup(cp);
            tmp.ptr = NULL;

            /*
             * Drop an end marker here so DEX loader can walk unfinished
             * list.
             */
            cpe[idx].kind = kCpeLastEntry;
            cpe[idx].fileName = NULL;
            cpe[idx].ptr = NULL;

            if (!prepareCpe(&tmp, false)) {
                /* drop from list and continue on */
                free(tmp.fileName);
            } else {
                /* copy over, pointers and all */
                cpe[idx] = tmp;
                idx++;
            }
        }

        cp += strlen(cp) +1;
    }
    assert(idx <= count);
    if (idx == 0 && !gDvm.optimizing) {
        /*
         * There's no way the vm will be doing anything if this is the
         * case, so just bail out (reasonably) gracefully.
         */
        //ALOGE("No valid entries found in bootclasspath '%s'", pathStr);
        gDvm.lastMessage = pathStr;
        dvmAbort();
    }

    LOGVV("  (filled %d of %d slots)", idx, count);

    /* put end marker in over-alloc slot */
    cpe[idx].kind = kCpeLastEntry;
    cpe[idx].fileName = NULL;
    cpe[idx].ptr = NULL;

    //dumpClassPath(cpe);

    free(mangle);
    gDvm.bootClassPath = cpe;
    return cpe;
}

void filterExempt(const char* className, ClassObject* resClass) {
    // filter interface
    if(dvmIsInterfaceClass(resClass)) {
        if(strcmp(className, "Ljava/lang/Iterable;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/Map;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/concurrent/ConcurrentMap;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/NavigableMap;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/concurrent/ConcurrentNavigableMap;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/SortedMap;") == 0) {
            exemptIfs->insert(resClass);
        //} else if(strcmp(className, "Ljavax/script/Bindings;") == 0) {
        //    exemptIfs->insert(resClass);
        //} else if(strcmp(className, "Ljavax/xml/ws/handler/MessageContext;") == 0) {
        //    exemptIfs->insert(resClass);
        //} else if(strcmp(className, "Ljavax/xml/ws/handler/LogicalMessageContext;") == 0) {
         //   exemptIfs->insert(resClass);
        //} else if(strcmp(className, "Ljavax/xml/ws/handler/soap/SOAPMessageContext;") == 0) {
        //    exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/Collection;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/List;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/Set;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/SortedSet;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/NavigableSet;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/Queue;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/concurrent/BlockingQueue;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/concurrent/TransferQueue;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/Deque;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/concurrent/BlockingDeque;") == 0) {
            exemptIfs->insert(resClass);
        //} else if(strcmp(className, "Ljava/nio/file/DirectoryStream;") == 0) {
        //    exemptIfs->insert(resClass);
        //} else if(strcmp(className, "Ljava/nio/file/SecureDirectoryStream;") == 0) {
        //    exemptIfs->insert(resClass);
        //} else if(strcmp(className, "Ljava/nio/file/Path;") == 0) {
        //    exemptIfs->insert(resClass);
        } else if(strcmp(className, "Landroid/os/IInterface;") == 0) {
            exemptIfs->insert(resClass);
        //} else if(strcmp(className, "Landroid/view/inputmethod/InputMethodSession;") == 0) {
        //    exemptIfs->insert(resClass);
        //} else if(strcmp(className, "Landroid/text/method/KeyListener;") == 0) {
        //    exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljavax/sip/ServerTransaction;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strncmp(className, "Landroid/os/Parcelable", 22) == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Landroid/os/IBinder;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/lang/Appendable;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/io/Closeable;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/lang/CharSequence;") == 0) {
            exemptIfs->insert(resClass);
        } else if(strcmp(className, "Ljava/util/Enumeration;") == 0) {
            exemptIfs->insert(resClass);
        //} else if(strcmp(className, "Lorg/apache/http/conn/OperatedClientConnection;") == 0) {
        //    exemptIfs->insert(resClass);
        }
    } else {
        // filter class
        if(strcmp(className, "Landroid/content/pm/PackageParser;") == 0) { // bad-alloc
            exemptClzs->insert(resClass);
        } else if(strcmp(className, "Landroid/telephony/TelephonyManager;") == 0) { // 
            exemptClzs->insert(resClass);
        /*} else if(strcmp(className, "Landroid/location/LocationManager$ListenerTransport$2;") == 0) { // bad-alloc
            exemptClzs->insert(resClass);
        } else if(strcmp(className, "Landroid/location/LocationManager$ListenerTransport$1;") == 0) { // bad-alloc
            exemptClzs->insert(resClass);
        } else if(strcmp(className, "Landroid/telephony/TelephonyManager;") == 0) { // bad-alloc
            exemptClzs->insert(resClass);
        } else if(strcmp(className, "Lcom/android/server/InputMethodManagerService$InputMethodSettings;") == 0) { // long-time
            exemptClzs->insert(resClass);
        } else if(strcmp(className, "Ljava/net/Socket;") == 0) { // too long-time, more than one day
            exemptClzs->insert(resClass);
        //} else if(strcmp(className, "Lorg/apache/harmony/xnet/provider/jsse/SSLSocketImpl;") == 0) { // too long-time, more than one day
        //    exemptClzs->insert(resClass);
        } else if(strcmp(className, "Lgov/nist/javax/sip/stack/UDPMessageChannel;") == 0) { // too long-time
            exemptClzs->insert(resClass);
        } else if(strcmp(className, "Lorg/apache/http/impl/conn/AbstractPoolEntry;") == 0) { // too long-time
            exemptClzs->insert(resClass);
        } else if(strcmp(className, "Lorg/apache/http/impl/conn/AbstractPoolEntry;") == 0) { // too long-time
            exemptClzs->insert(resClass);
        } else if(strcmp(className, "Lorg/apache/http/impl/client/DefaultRequestDirector;") == 0) { // too long-time
            exemptClzs->insert(resClass);*/
        } else if(strcmp(className, "Lcom/android/internal/telephony/cat/CatService$1;") == 0) { // take too long
            exemptClzs->insert(resClass);
        } else {
            for(std::set<ClassObject*>::iterator it = exemptClzs->begin(); it != exemptClzs->end(); it++) {
                if(dvmInstanceof(resClass, *it)) {
                    exemptClzs->insert(resClass);
                    break;
                }
            }
            for(std::set<ClassObject*>::iterator it = exemptIfs->begin(); it != exemptIfs->end(); it++) {
                if(dvmImplements(resClass, *it)) {
                    exemptClzs->insert(resClass);
                    break;
                }
            }
        }
    }
}

void getPackageName(char* filepath, char* packageName, int len) {
    char cmd[250];
    strcpy(cmd, "./aapt dump badging ");
    strcat(cmd, filepath);
    strcat(cmd, " | grep package | awk '{print $2}' | sed s/name=//g | sed s/\\'//g");
    FILE* pipe = popen(cmd, "r");
    if (!pipe) return;
    fgets(packageName, len, pipe);
    // get rid of the newline character
    if(packageName[strlen(packageName) - 1] == '\n') {
        packageName[strlen(packageName) - 1] = '\0';
    }
    pclose(pipe);
}

//extern int timeuse;
extern int maxtime; 
//extern int maxit;
//extern Method* maxMethod;
//extern int counts;

void loadApk(char* apkPath, char* flag, int maxSubClass) {
    MaxSubCount = maxSubClass;
    struct timeval start, end;
    gettimeofday(&start, NULL);
    ClassPathEntry* entry;
    const char* bootPath = "/local_scratch/jars/core.jar:/local_scratch/jars/core-junit.jar:/local_scratch/jars/bouncycastle.jar:/local_scratch/jars/ext.jar:/local_scratch/jars/framework.jar:/local_scratch/jars/framework2.jar:/local_scratch/jars/android.policy.jar:/local_scratch/jars/services.jar:/local_scratch/jars/apache-xml.jar:";
    bool isKernelParse = (strcmp(flag, "-k") == 0);
    bool reuse = (strcmp(flag, "-r") == 0);
    char* classPath;
    if(isKernelParse) {
        classPath = new char[strlen(bootPath) + 1];
        strcpy(classPath, bootPath);
    } else {
        classPath = new char[strlen(bootPath) + strlen(apkPath) + 1];
        strcpy(classPath, bootPath);
        strcat(classPath, apkPath);
    }
    entry = processClassPath(classPath);
    delete[] classPath;
    while (entry->kind != kCpeLastEntry) {
        DvmDex* pDvmDex;
        switch (entry->kind) {
        case kCpeJar:
            {
                JarFile* pJarFile = (JarFile*) entry->ptr;
                pDvmDex = dvmGetJarFileDex(pJarFile);
            }
            break;
        case kCpeDex:
            {
                RawDexFile* pRawDexFile = (RawDexFile*) entry->ptr;
                 pDvmDex = dvmGetRawDexFileDex(pRawDexFile);
            }
            break;
        default:
            //ALOGE("Unknown kind %d", entry->kind);
            assert(false);
            return;
        }
        loadedDex.push_back(pDvmDex);
        pDvmDex->pDexFile->pClassLookup = dexCreateClassLookup(pDvmDex->pDexFile);
        entry++;
    }
//        makeClassLoader(&loadedDex);    
    for(unsigned int idx = 0; idx < loadedDex.size(); idx++) {
        DvmDex* pDvmDex;
        pDvmDex = loadedDex[idx];
//      Object* classLoader = pDvmDex->classLoader;
        for(unsigned int i = 0; i < pDvmDex->pHeader->classDefsSize; i++) {
            const DexClassDef pClassDef = pDvmDex->pDexFile->pClassDefs[i];
            ClassObject* resClass;  // this segment is copied from Resolve.cpp - dvmResolveClass()
            const char* className;
            className = dexStringByTypeIdx(pDvmDex->pDexFile, pClassDef.classIdx);
            /*if(strncmp(className, "Landroid/support/v4", 19) == 0) {
                continue;
            }
            if(strncmp(className, "Ledu/utk/offloadtest/MainActivity;", 34) != 0) {
                ALOGE("parsing find main activity at idx: %d, total: %d", idx, loadedDex.size());
            }*/
            if(className[0] != '\0' && className[1] == '\0') {
                /* primitive type */
                resClass = dvmFindPrimitiveClass(className[0]);
            } else {
                //resClass = dvmFindClassNoInit(className, classLoader);
                resClass = customDefineClass(pDvmDex, className, NULL);
                if(strcmp(className, "Ljava/lang/Object;") == 0 && javaLangObject == NULL) {
                    javaLangObject = resClass;
                }
                if(resClass == NULL) {
                    //ALOGE("find unloaded class: %s", className);
                    continue;
                }
                filterExempt(className, resClass);
            }
        }
    }
    /*for(unsigned int i = 0; i < exemptClzs->size(); i++) {
        ALOGE("exempt clazz: %s", exemptClzs->at(i)->descriptor);
    }*/
    char outFileName[160];
    const char* BASE_PATH = "/local_scratch/jars/results/argument";
    if(BASE_PATH == NULL) {
        BASE_PATH = strdup("/data/data");
    }
    strcpy(outFileName, BASE_PATH);
    strcat(outFileName, "/");
    //char packageName[80];
    //getPackageName(apkPath, packageName, 80);
    //strcat(outFileName, packageName);
    basePath = strdup(outFileName);

    openFiles(reuse);
    //createStringDict();
    loadStringDict();
    if(!isKernelParse && reuse) {
        loadParsedMethodOffInfo();
        filterInherited();
    }

    unsigned int toRunMax = 1;
    if(isKernelParse) {
        toRunMax = loadedDex.size();
    }
    for(unsigned int idx = 0; idx < toRunMax; idx++) {
        DvmDex* pDvmDex;
        if(isKernelParse) {
            pDvmDex = loadedDex[idx];
        } else {
            pDvmDex = loadedDex[loadedDex.size() - idx - 1];
        }
        for(unsigned int i = 0; i < pDvmDex->pHeader->classDefsSize; i++) {
            const DexClassDef pClassDef = pDvmDex->pDexFile->pClassDefs[i];
            ClassObject* resClass;  // this segment is copied from Resolve.cpp - dvmResolveClass()
            const char* className;
            className = dexStringByTypeIdx(pDvmDex->pDexFile, pClassDef.classIdx);
            if(strncmp(className, "Landroid/support/v4", 19) == 0) {
                continue;
            }
            /*if(strncmp(className, "Ledu/utk/offloadtest/MainActivity;", 34) != 0) {
                continue;
            }*/

            if(className[0] != '\0' && className[1] == '\0') {
                /* primitive type */
                resClass = dvmFindPrimitiveClass(className[0]);
            } else {
                resClass = dvmLookupClass(className, NULL, false);
            }
            if(resClass == NULL) {
                //ALOGE("find unloaded class: %s", className);
                continue;
            }
            // check if it is an interface
            if(dvmIsInterfaceClass(resClass)) {
                continue;
            }
            if(exemptClzs->find(resClass) != exemptClzs->end()) {
                continue;
            }
            // traverse and parse every method in the class, see Object.cpp - findMethodInListByDescriptor
            Method* vmethods = resClass->virtualMethods;
            size_t vmethodCount = resClass->virtualMethodCount;
            for(size_t j = 0; j < vmethodCount; j++) {
                Method* method = &vmethods[j];
                if(dvmIsNativeMethod(method)) {
                    continue;
                }
                //if(strcmp(method->clazz->descriptor, "Ljava/util/GregorianCalendar;") == 0 && strcmp(method->name, "computeTime") == 0) {
                //if(strcmp(method->clazz->descriptor, "Ledu/utk/offloadtest/MainActivity;") == 0 && strcmp(method->name, "matrixTest") == 0) {
                //if((strcmp(method->clazz->descriptor, "Lcom/leslie/cjpokeroddscalculator/CJPokerOddsCalculator$3;") == 0 && strcmp(method->name, "poker_calculation") == 0)
                //        || (!strcmp(method->clazz->descriptor, "Lcom/mechsoft/ru/graph/Graph;") && !strcmp(method->name, "TheShortestPathByTime"))
                //        || (!strcmp(method->clazz->descriptor, "Lcom/mechsoft/ru/graph/Graph;") && !strcmp(method->name, "Dijkstra"))
                //        || (!strcmp(method->clazz->descriptor, "Lcom/mechsoft/ru/graph/Graph;") && !strcmp(method->name, "TheShortestPathByTransfer"))) { // long time execution - 5m
                //    ALOGE("start parse method: %s:%s, %u", method->clazz->descriptor, method->name, method->idx);
                std::vector<Method*>* chain = new std::vector<Method*>();
                MethodAccInfo* methodAccInfo = new MethodAccInfo();
                methodAccInfo->method = method;
                parseMethod(methodAccInfo, chain);
                assert(chain->empty());
                delete chain;
                persistMethodInfo(methodAccInfo, "/home/yli118/local_scratch/android/branches/COMET/vm_test/data/parse/parse.txt");
                freeMethodAccInfo(methodAccInfo);
                //}
            }
            Method* dmethods = resClass->directMethods;
            size_t dmethodCount = resClass->directMethodCount;
            for(size_t j = 0; j < dmethodCount; j++) {
                Method* method = &dmethods[j];
                if(dvmIsNativeMethod(method)) {
                    continue;
                }
                //if((strcmp(method->clazz->descriptor, "Ljava/util/Properties;") == 0)
                //  || (strcmp(method->clazz->descriptor, "Ljava/net/ContentHandler;") == 0)) { //&& strcmp(method->name, "printStackTrace") == 0)
                        //|| (strcmp(method->clazz->descriptor, "Ljava/lang/Throwable;") == 0 && strcmp(method->name, "addSuppressed") == 0)) {
               //     continue;
                //}
                //if(strcmp(method->clazz->descriptor, "Ljava/util/GregorianCalendar;") == 0 && strcmp(method->name, "computeTime") == 0) {
                //if(strcmp(method->clazz->descriptor, "Ledu/utk/offloadtest/MainActivity;") == 0 && strcmp(method->name, "matrixTest") == 0) {
                //if((strcmp(method->clazz->descriptor, "Lcom/leslie/cjpokeroddscalculator/CJPokerOddsCalculator$3;") == 0 && strcmp(method->name, "poker_calculation") == 0)
                //        || (!strcmp(method->clazz->descriptor, "Lcom/mechsoft/ru/graph/Graph;") && !strcmp(method->name, "TheShortestPathByTime"))
                //        || (!strcmp(method->clazz->descriptor, "Lcom/mechsoft/ru/graph/Graph;") && !strcmp(method->name, "Dijkstra"))
                //        || (!strcmp(method->clazz->descriptor, "Lcom/mechsoft/ru/graph/Graph;") && !strcmp(method->name, "TheShortestPathByTransfer"))) {
                //    ALOGE("start parse method: %s:%s, %u", method->clazz->descriptor, method->name, method->idx);
                std::vector<Method*>* chain = new std::vector<Method*>();
                MethodAccInfo* methodAccInfo = new MethodAccInfo();
                methodAccInfo->method = method;
                parseMethod(methodAccInfo, chain);
                assert(chain->empty());
                delete chain;
                persistMethodInfo(methodAccInfo, "/home/yli118/local_scratch/android/branches/COMET/vm_test/data/parse/parse.txt");
                freeMethodAccInfo(methodAccInfo);
                //}
            }
        }
    }
    closeFiles();
    /*gDvm.methodAccMap = new std::map<char*, MethodAccResult*, charscomp>();
    retrieveMethodInfo(gDvm.methodAccMap, outFileName);
    ALOGE("method ACc vec size: %u", gDvm.methodAccMap->size());
    for (std::map<char*, MethodAccResult*>::iterator it = gDvm.methodAccMap->begin(); it != gDvm.methodAccMap->end(); ++it) {
        MethodAccResult* methodAccResult = it->second;
        ALOGE("parse result, %s", it->first);
        for(unsigned int j = 0; j < methodAccResult->args->size(); j++) {
        //    ALOGE("methodParser: for arg %d: ", j);
            depthTraverseResult(methodAccResult->args->at(j), 1);
        }
        for(unsigned int j = 0; j < methodAccResult->globalClazz->size(); j++) {
        //    ALOGE("methodParser: for clazz %s: ", methodAccResult->globalClazz->at(j)->clazz);
            depthTraverseResult(methodAccResult->globalClazz->at(j), 1);
        }
    }*/
    gettimeofday(&end, NULL);
    int timeuse = (1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec) / 1000;

    ALOGE("total arguments with sub %d time use is: %d, maxtime: %d", maxSubClass, timeuse, maxtime / 1000);
}
