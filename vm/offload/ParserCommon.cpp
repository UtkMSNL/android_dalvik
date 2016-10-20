#include "Dalvik.h"
#include "CustomizedClass.h"
#include "libdex/DexCatch.h"
#include "ParserCommon.h"

char* basePath;
std::vector<DvmDex*> loadedDex;
std::fstream strDictFile;
std::map<const char*, int, charscomp>* strOffMap = new std::map<const char*, int, charscomp>();
std::map<int, const char*>* offStrMap = new std::map<int, const char*>();
std::map<ClassObject*, std::vector<ClassObject*>* > subclassMap;
std::map<ClassObject*, std::vector<ClassObject*>* > implclassMap;

ClassObject* resolveClass(const ClassObject* referrer, u4 classIdx,
    bool fromUnverifiedConstant)
{
    DvmDex* pDvmDex = referrer->pDvmDex;
    ClassObject* resClass;
    const char* className;

    /*
     * Check the table first -- this gets called from the other "resolve"
     * methods.
     */
    resClass = dvmDexGetResolvedClass(pDvmDex, classIdx);
    if (resClass != NULL)
        return resClass;

    /*
     * Class hasn't been loaded yet, or is in the process of being loaded
     * and initialized now.  Try to get a copy.  If we find one, put the
     * pointer in the DexTypeId.  There isn't a race condition here --
     * 32-bit writes are guaranteed atomic on all target platforms.  Worst
     * case we have two threads storing the same value.
     *
     * If this is an array class, we'll generate it here.
     */
    className = dexStringByTypeIdx(pDvmDex->pDexFile, classIdx);
    if (className[0] != '\0' && className[1] == '\0') {
        /* primitive type */
        resClass = dvmFindPrimitiveClass(className[0]);
    } else {
        resClass = customFindClassNoInit(className, referrer->classLoader);
    }

    if (resClass != NULL) {
        if (!fromUnverifiedConstant &&
            IS_CLASS_FLAG_SET(referrer, CLASS_ISPREVERIFIED))
        {
            ClassObject* resClassCheck = resClass;
            if (dvmIsArrayClass(resClassCheck))
                resClassCheck = resClassCheck->elementClass;

            if (referrer->pDvmDex != resClassCheck->pDvmDex &&
                resClassCheck->classLoader != NULL)
            {
                dvmThrowIllegalAccessError(
                    "Class ref in pre-verified class resolved to unexpected "
                    "implementation");
                return NULL;
            }
        }

        dvmDexSetResolvedClass(pDvmDex, classIdx, resClass);
    } else {
        /* not found, exception should be raised */
        //ALOGE("Class not found: %s",
        //    dexStringByTypeIdx(pDvmDex->pDexFile, classIdx));
    }
    
    return resClass;
}

Method* resolveMethod(const ClassObject* referrer, u4 methodIdx,
    MethodType methodType) {
    DvmDex* pDvmDex = referrer->pDvmDex;
    ClassObject* resClass;
    const DexMethodId* pMethodId;
    Method* resMethod;

    assert(methodType != METHOD_INTERFACE);

    pMethodId = dexGetMethodId(pDvmDex->pDexFile, methodIdx);

    resClass = resolveClass(referrer, pMethodId->classIdx, false);
    if(resClass == NULL) {
        return NULL;
    }

    const char* name = dexStringById(pDvmDex->pDexFile, pMethodId->nameIdx);
    DexProto proto;
    dexProtoSetFromMethodId(&proto, pDvmDex->pDexFile, pMethodId);

    /*
     * We need to chase up the class hierarchy to find methods defined
     * in super-classes.  (We only want to check the current class
     * if we're looking for a constructor; since DIRECT calls are only
     * for constructors and private methods, we don't want to walk up.)
     */
    if (methodType == METHOD_DIRECT) {
        resMethod = dvmFindDirectMethod(resClass, name, &proto);
    } else if (methodType == METHOD_STATIC) {
        resMethod = dvmFindDirectMethodHier(resClass, name, &proto);
    } else {
        resMethod = dvmFindVirtualMethodHier(resClass, name, &proto);
    }

    if(resMethod == NULL) {
        //ALOGE("find error method, the name is: %s, resClass is: %s", name, resClass->descriptor);
    }
    dvmDexSetResolvedMethod(pDvmDex, methodIdx, resMethod);
    
    return resMethod;
}

/*
 * Resolve an interface method reference.
 *
 * Returns NULL with an exception raised on failure.
 */
Method* resolveInterfaceMethod(const ClassObject* referrer, u4 methodIdx)
{
    DvmDex* pDvmDex = referrer->pDvmDex;
    ClassObject* resClass;
    const DexMethodId* pMethodId;
    Method* resMethod;

    pMethodId = dexGetMethodId(pDvmDex->pDexFile, methodIdx);

    resClass = resolveClass(referrer, pMethodId->classIdx, false);
    if (resClass == NULL) {
        return NULL;
    }
    if (!dvmIsInterfaceClass(resClass)) {
        /* whoops */
        dvmThrowIncompatibleClassChangeErrorWithClassMessage(
                resClass->descriptor);
        return NULL;
    }

    const char* methodName =
        dexStringById(pDvmDex->pDexFile, pMethodId->nameIdx);

    DexProto proto;
    dexProtoSetFromMethodId(&proto, pDvmDex->pDexFile, pMethodId);

    resMethod = dvmFindInterfaceMethodHier(resClass, methodName, &proto);
    if (resMethod == NULL) {
        //ALOGE("find error method, the name is: %s, resClass is: %s", methodName, resClass->descriptor);
    }

    dvmDexSetResolvedMethod(pDvmDex, methodIdx, resMethod);

    return resMethod;
}

/*
 * Resolve an instance field reference.
 *
 * Returns NULL and throws an exception on error (no such field, illegal
 * access).
 */
InstField* resolveInstField(const ClassObject* referrer, u4 ifieldIdx)
{
    DvmDex* pDvmDex = referrer->pDvmDex;
    ClassObject* resClass;
    const DexFieldId* pFieldId;
    InstField* resField;

    pFieldId = dexGetFieldId(pDvmDex->pDexFile, ifieldIdx);

    /*
     * Find the field's class.
     */
    resClass = resolveClass(referrer, pFieldId->classIdx, false);
    if(resClass == NULL) {
        return NULL;
    }

    resField = dvmFindInstanceFieldHier(resClass,
        dexStringById(pDvmDex->pDexFile, pFieldId->nameIdx),
        dexStringByTypeIdx(pDvmDex->pDexFile, pFieldId->typeIdx));
        
    if(resField == NULL) {
        ALOGE("find error field, the name is: %s, resClass is: %s", dexStringById(pDvmDex->pDexFile, pFieldId->nameIdx), resClass->descriptor);
    }
    dvmDexSetResolvedField(pDvmDex, ifieldIdx, (Field*)resField);
    
    return resField;
}

/*
 * Resolve a static field reference.  The DexFile format doesn't distinguish
 * between static and instance field references, so the "resolved" pointer
 * in the Dex struct will have the wrong type.  We trivially cast it here.
 *
 * Causes the field's class to be initialized.
 */
StaticField* resolveStaticField(const ClassObject* referrer, u4 sfieldIdx)
{
    DvmDex* pDvmDex = referrer->pDvmDex;
    ClassObject* resClass;
    const DexFieldId* pFieldId;
    StaticField* resField;

    pFieldId = dexGetFieldId(pDvmDex->pDexFile, sfieldIdx);

    /*
     * Find the field's class.
     */
    resClass = resolveClass(referrer, pFieldId->classIdx, false);
    if(resClass == NULL) {
        return NULL;
    }

    resField = dvmFindStaticFieldHier(resClass,
                dexStringById(pDvmDex->pDexFile, pFieldId->nameIdx),
                dexStringByTypeIdx(pDvmDex->pDexFile, pFieldId->typeIdx));
    if(resField == NULL) {
        ALOGE("find error field, the name is: %s, resClass is: %s", dexStringById(pDvmDex->pDexFile, pFieldId->nameIdx), resClass->descriptor);
    }
    
    dvmDexSetResolvedField(pDvmDex, sfieldIdx, (Field*) resField);
    return resField;
}

void createStringDict() {
    std::map<const char*, int, charscomp> strdict;
    int offset = 0;
    for(unsigned int idx = 0; idx < loadedDex.size(); idx++) {
        DvmDex* pDvmDex;
        pDvmDex = loadedDex[idx];
        for(unsigned int i = 0; i < pDvmDex->pHeader->classDefsSize; i++) {
            const DexClassDef pClassDef = pDvmDex->pDexFile->pClassDefs[i];
            ClassObject* resClass;  // this segment is copied from Resolve.cpp - dvmResolveClass()
            const char* className;
            className = dexStringByTypeIdx(pDvmDex->pDexFile, pClassDef.classIdx);
            if(className[0] != '\0' && className[1] == '\0') {
                /* primitive type */
                resClass = dvmFindPrimitiveClass(className[0]);
            } else {
                resClass = dvmLookupClass(className, NULL, false);
            }
            if(resClass == NULL) {
                ALOGE("find unloaded class: %s", className);
                continue;
            }
            if(strdict.find(className) == strdict.end()) {
                strdict[className] = offset++;
            }
            // traverse and parse every method in the class, see Object.cpp - findMethodInListByDescriptor
            Method* vmethods = resClass->virtualMethods;
            size_t vmethodCount = resClass->virtualMethodCount;
            for(size_t j = 0; j < vmethodCount; j++) {
                Method* method = &vmethods[j];
                if(strdict.find(method->name) == strdict.end()) {
                    strdict[method->name] = offset++;
                }
            }
            Method* dmethods = resClass->directMethods;
            size_t dmethodCount = resClass->directMethodCount;
            for(size_t j = 0; j < dmethodCount; j++) {
                Method* method = &dmethods[j];
                if(strdict.find(method->name) == strdict.end()) {
                    strdict[method->name] = offset++;
                }
            }
        }
    }
    char terminCh = '\0';
    strDictFile.seekp(0, std::ios::end);
    for(std::map<const char*, int, charscomp>::iterator it = strdict.begin(); it != strdict.end(); ++it) {
        strDictFile.write(it->first, strlen(it->first));
        strDictFile.write(&terminCh, 1);
        strDictFile.write(reinterpret_cast<char*>(&(it->second)), sizeof(int));
    }
}

void loadStringDict() {
    char dictFileName[160];
    strcpy(dictFileName, basePath);
    strcat(dictFileName, "/strdict.bin");
    strDictFile.open(dictFileName, std::ios::in | std::ios::out | std::ios::binary);
    std::streampos begin, end;
    strDictFile.seekg(0, std::ios::end);
    end = strDictFile.tellg();
    strDictFile.seekg(0, std::ios::beg);
    begin = strDictFile.tellg();
    unsigned int total = end - begin;
    if(total == 0) {
        createStringDict();
    }
    char readbuffer[total];
    strDictFile.read(readbuffer, total);
    char* buffer = readbuffer;
    int leftbytes = total;
    while(leftbytes > 0) {
        int index = 0;
        while(buffer[index] != '\0') {
            index++;
        }
        char* str = new char[index + 1];
        memcpy(str, buffer, index);
        str[index] = '\0';
        buffer += (index + 1);
        int offset;
        memcpy(&offset, buffer, sizeof(offset));
        buffer += sizeof(offset);
        leftbytes -= (index + 1 + sizeof(offset));
        (*strOffMap)[str] = offset;
        (*offStrMap)[offset] = str;
    }

    // load Additional Dict
    int offset = strOffMap->size();
    for(unsigned int idx = 0; idx < loadedDex.size(); idx++) {
        DvmDex* pDvmDex;
        pDvmDex = loadedDex[idx];
        for(unsigned int i = 0; i < pDvmDex->pHeader->classDefsSize; i++) {
            const DexClassDef pClassDef = pDvmDex->pDexFile->pClassDefs[i];
            ClassObject* resClass;  // this segment is copied from Resolve.cpp - dvmResolveClass()
            const char* className;
            className = dexStringByTypeIdx(pDvmDex->pDexFile, pClassDef.classIdx);
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
            if(strOffMap->find(className) == strOffMap->end()) {
                (*strOffMap)[className] = offset;
                (*offStrMap)[offset] = className;
                offset++;
            }
            // traverse and parse every method in the class, see Object.cpp - findMethodInListByDescriptor
            Method* vmethods = resClass->virtualMethods;
            size_t vmethodCount = resClass->virtualMethodCount;
            for(size_t j = 0; j < vmethodCount; j++) {
                Method* method = &vmethods[j];
                if(strOffMap->find(method->name) == strOffMap->end()) {
                    (*strOffMap)[method->name] = offset;
                    (*offStrMap)[offset] = method->name;
                    offset++;
                }
            }
            Method* dmethods = resClass->directMethods;
            size_t dmethodCount = resClass->directMethodCount;
            for(size_t j = 0; j < dmethodCount; j++) {
                Method* method = &dmethods[j];
                if(strOffMap->find(method->name) == strOffMap->end()) {
                    (*strOffMap)[method->name] = offset;
                    (*offStrMap)[offset] = method->name;
                    offset++;
                }
            }
        }
    }
    strDictFile.close();
}

std::vector<ClassObject*>* findSubClass(ClassObject* clazz) {
    if(subclassMap.find(clazz) != subclassMap.end()) {
        return subclassMap[clazz];
    }
    std::vector<ClassObject*>* result = new std::vector<ClassObject*>();
    subclassMap[clazz] = result;
    for(unsigned int idx = 0; idx < loadedDex.size(); idx++) {
        DvmDex* pDvmDex;
        pDvmDex = loadedDex[idx];
    
        // iterate the dvm classes and parse each method in the class
        for(unsigned int j = 0; j < pDvmDex->pHeader->classDefsSize; j++) {
            const DexClassDef pClassDef = pDvmDex->pDexFile->pClassDefs[j];
            ClassObject* resClass;  // this segment is copied from Resolve.cpp - dvmResolveClass()
            const char* className;
            className = dexStringByTypeIdx(pDvmDex->pDexFile, pClassDef.classIdx);
            if(className[0] != '\0' && className[1] == '\0') {
                /* primitive type */
                resClass = dvmFindPrimitiveClass(className[0]);
            } else {
                resClass = dvmLookupClass(className, NULL, false);
            }
            if(resClass == NULL) {
                continue;
            }
            // check if it is an interface
            if(dvmIsInterfaceClass(resClass)) {
                continue;
            }
            // check if is subclass
            if(dvmInstanceof(resClass, clazz)) {
                result->push_back(resClass);
            }
        }
    }
    return result;
    /*for(unsigned int i = 0; i < (*result).size(); i++) {
        ALOGE("findsubclass class: %s", (*result)[i]->descriptor);
    }*/
}

std::vector<ClassObject*>* findImplementClass(ClassObject* clazz) {
    if(implclassMap.find(clazz) != implclassMap.end()) {
        return implclassMap[clazz];
    }
    std::vector<ClassObject*>* result = new std::vector<ClassObject*>();
    implclassMap[clazz] = result;
    for(unsigned int idx = 0; idx < loadedDex.size(); idx++) {
        DvmDex* pDvmDex;
        pDvmDex = loadedDex[idx];
    
        // iterate the dvm classes and parse each method in the class
        for(unsigned int j = 0; j < pDvmDex->pHeader->classDefsSize; j++) {
            const DexClassDef pClassDef = pDvmDex->pDexFile->pClassDefs[j];
            ClassObject* resClass;  // this segment is copied from Resolve.cpp - dvmResolveClass()
            const char* className;
            className = dexStringByTypeIdx(pDvmDex->pDexFile, pClassDef.classIdx);
            if(className[0] != '\0' && className[1] == '\0') {
                /* primitive type */
                resClass = dvmFindPrimitiveClass(className[0]);
            } else {
                resClass = dvmLookupClass(className, NULL, false);
            }
            if(resClass == NULL) {
                continue;
            }
            // check if it is an interface
            if(dvmIsInterfaceClass(resClass)) {
                continue;
            }
            // check if is subclass
            if(dvmImplements(resClass, clazz)) {
                result->push_back(resClass);
            }
        }
    }
    return result;
   /* for(unsigned int i = 0; i < (*result).size(); i++) {
        ALOGE("findimplementedclass class: %s", (*result)[i]->descriptor);
    }*/
}
