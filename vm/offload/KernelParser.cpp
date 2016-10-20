
#include "Dalvik.h"
#include "CustomizedClass.h"
#include "libdex/DexCatch.h"

int MaxBranchDepth = INT_MAX;
unsigned int MaxSubCount = INT_MAX;

extern std::vector<DvmDex*> loadedDex;
extern ClassObject* javaLangObject;
extern std::vector<ClassObject*>* exemptClzs;
extern std::vector<ClassObject*>* exemptIfs;
std::map<Method*, MethodAccInfo*> methodResMap;
std::map<Method*, MethodAccInfo*> virtualResMap;
std::map<Method*, MethodAccInfo*> interResMap;
std::map<Method*, std::map<ClassObject*, BitsVec*>* > methodStaticMap;
std::map<ClassObject*, std::vector<ClassObject*>* > subclassMap;
std::map<ClassObject*, std::vector<ClassObject*>* > implclassMap;

// method declaration
void parseInsns(const u2* insns, MethodAccInfo* methodAccInfo, std::set<Method*>* chain, std::vector<int>* insOffsets, std::map<u2, std::set<ObjectAccInfo*> >* interestRegObjMap, int depth, bool* exitMethod);

u2 inst_a(const u2* insns) {
    return (*insns >> 8) & 0x0f;
}

u2 inst_b(const u2* insns) {
    return *insns >> 12;
}

u2 inst_aa(const u2* insns) {
    return *insns >> 8;
}

#if __BYTE_ORDER == __LITTLE_ENDIAN
static inline s4 s4FromSwitchData(const void* switchData) {
    return *(s4*) switchData;
}
#else
static inline s4 s4FromSwitchData(const void* switchData) {
    u2* data = switchData;
    return data[0] | (((s4) data[1]) << 16);
}
#endif

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
        ALOGE("Class not found: %s",
            dexStringByTypeIdx(pDvmDex->pDexFile, classIdx));
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
        ALOGE("find error method, the name is: %s, resClass is: %s", name, resClass->descriptor);
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
        ALOGE("find error method, the name is: %s, resClass is: %s", methodName, resClass->descriptor);
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

static void freeObjectAccInfo(ObjectAccInfo* objAccInfo) {
    if(objAccInfo == NULL) {
        return;
    }
    for(unsigned int i = 0; i < objAccInfo->fieldSet.size(); i++) {
        freeObjectAccInfo(objAccInfo->fieldSet[i]);
        if(objAccInfo->trackSet[i] != NULL) {
            delete objAccInfo->trackSet[i];
        }
    }
    delete objAccInfo;
}

void freeMethodAccInfo(MethodAccInfo* methodAccInfo) {
    for(unsigned int i = 0; i < methodAccInfo->args->size(); i++) {
        freeObjectAccInfo(methodAccInfo->args->at(i));
    }
    delete methodAccInfo->args;
    if(methodAccInfo->globalClazz != NULL) {
        for(unsigned int i = 0; i < methodAccInfo->globalClazz->size(); i++) {
            freeObjectAccInfo(methodAccInfo->globalClazz->at(i));
        }
        delete methodAccInfo->globalClazz;
    }
    if(methodAccInfo->returnObjs != NULL) {
        delete methodAccInfo->returnObjs;
    }
    if(methodAccInfo->curMethodReturns != NULL) {
        delete methodAccInfo->curMethodReturns;
    }
}

void populateMethodAccInfo(MethodAccInfo* methodAccInfo) {
    Method* method = methodAccInfo->method;
    methodAccInfo->args = new std::vector<ObjectAccInfo*>();
    for(int i = 0; i < method->insSize; i++) {
        methodAccInfo->args->push_back(new ObjectAccInfo());
    }
    methodAccInfo->globalClazz = new std::vector<ClazzAccInfo*>();
}

/* check if this object or its parent has been flagged as migrating all */
static bool isObjFlagedAll(ObjectAccInfo* objAccInfo) {
    ObjectAccInfo* tmp = objAccInfo;
    do {
        if(tmp->allFlag) {
            return true;
        }
        tmp = tmp->belonging;
    } while(tmp != NULL);
    return false;
}

static bool isFlagedAllImpl(ObjectAccInfo* objAccInfo, std::set<ObjectAccInfo*>* chain) {
    if(chain->find(objAccInfo) != chain->end()) {
        return true;
    }
    if(!isObjFlagedAll(objAccInfo)) {
        return false;
    }
    chain->insert(objAccInfo);
    for(unsigned int i = 0; i < objAccInfo->trackSet.size(); i++) {
        if(objAccInfo->trackSet[i] == NULL) {
            continue;
        }
        for(std::set<ObjectAccInfo*>::iterator it = objAccInfo->trackSet[i]->begin(); it != objAccInfo->trackSet[i]->end(); ++it) {
            if(!isFlagedAllImpl(*it, chain)) {
                return false;
            }
        }
    }
    chain->erase(objAccInfo);
    return true;
}

/* check if the objects in the vector are all flaged as migrating all */
static bool isVecFlagedAll(std::set<ObjectAccInfo*>* objsVector) {
    if(objsVector == NULL) {
        return true;
    }
    for(std::set<ObjectAccInfo*>::iterator it = objsVector->begin(); it != objsVector->end(); ++it) {
        std::set<ObjectAccInfo*> chain;
        if(!isFlagedAllImpl(*it, &chain)) {
            return false;
        }
    }
    return true;
}

static void flagObjALLImpl(ObjectAccInfo* objAccInfo, std::set<ObjectAccInfo*>* chain) {
    if(objAccInfo == NULL) {
        return;
    }
    if(chain->find(objAccInfo) != chain->end()) {
        return;
    }
    chain->insert(objAccInfo);
    objAccInfo->allFlag = true;
    for(unsigned int i = 0; i < objAccInfo->fieldSet.size(); i++) {
        if(objAccInfo->trackSet[i] == NULL) {
            continue;
        }
        for(std::set<ObjectAccInfo*>::iterator it = objAccInfo->trackSet[i]->begin(); it != objAccInfo->trackSet[i]->end(); ++it) {
            flagObjALLImpl(*it, chain);
        }
    }
    chain->erase(objAccInfo);
}

static void flagObjAll(ObjectAccInfo* objAccInfo) {
    std::set<ObjectAccInfo*> chain;
    flagObjALLImpl(objAccInfo, &chain);
}

/* flag all the objects in vector as migrating all */
static void flagVecAll(std::set<ObjectAccInfo*>* objsVector) {
    for(std::set<ObjectAccInfo*>::iterator it = objsVector->begin(); it != objsVector->end(); ++it) {
        flagObjAll(*it);
    }
}

static void flagObjALLArrayImpl(ObjectAccInfo* objAccInfo, std::set<ObjectAccInfo*>* chain) {
    if(objAccInfo == NULL) {
        return;
    }
    if(chain->find(objAccInfo) != chain->end()) {
        return;
    }
    chain->insert(objAccInfo);
    objAccInfo->allFlag = true;
    objAccInfo->inArray = true;
    for(unsigned int i = 0; i < objAccInfo->fieldSet.size(); i++) {
        if(objAccInfo->trackSet[i] == NULL) {
            continue;
        }
        for(std::set<ObjectAccInfo*>::iterator it = objAccInfo->trackSet[i]->begin(); it != objAccInfo->trackSet[i]->end(); ++it) {
            flagObjALLArrayImpl(*it, chain);
        }
    }
    chain->erase(objAccInfo);
}

static void flagObjAllArray(ObjectAccInfo* objAccInfo) {
    std::set<ObjectAccInfo*> chain;
    flagObjALLArrayImpl(objAccInfo, &chain);
}

/* flag all the objects in vector as migrating all */
static void flagVecAllArray(std::set<ObjectAccInfo*>* objsVector) {
    for(std::set<ObjectAccInfo*>::iterator it = objsVector->begin(); it != objsVector->end(); ++it) {
        flagObjAllArray(*it);
    }
}

/*static void pushSingle(std::vector<ObjectAccInfo*>* dst, ObjectAccInfo* obj) {
    bool inDst = false;
    for(unsigned int j = 0; j < dst->size(); j++) {
        if(obj == dst->at(j)) {
            inDst = true;
            break;
        }
    }
    if(!inDst) {
        dst->push_back(obj);
    }
}

static void pushVec(std::vector<ObjectAccInfo*>* dst, std::vector<ObjectAccInfo*>* src) {
    for(unsigned int i = 0; i < src->size(); i++) {
        pushSingle(dst, src->at(i));
    }
}*/

static void unionObjectFieldInfo(ObjectAccInfo* dstObjAccInfo, ObjectAccInfo* srcObjAccInfo, std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap) {
    (*addrMap)[srcObjAccInfo] = dstObjAccInfo;
    if(srcObjAccInfo->allFlag) {
        dstObjAccInfo->allFlag = true;
    }
    if(srcObjAccInfo->inArray) {
        dstObjAccInfo->inArray = true;
    }
    if(dstObjAccInfo->fieldSet.size() < srcObjAccInfo->fieldSet.size()) {
        dstObjAccInfo->fieldSet.resize(srcObjAccInfo->fieldSet.size());
        dstObjAccInfo->trackSet.resize(srcObjAccInfo->trackSet.size());
    }
    for(unsigned int i = 0; i < srcObjAccInfo->fieldSet.size(); i++) {
        if(srcObjAccInfo->fieldSet[i] == NULL) {
            continue;
        }
        if(dstObjAccInfo->fieldSet[i] == NULL) {
            dstObjAccInfo->fieldSet[i] = new ObjectAccInfo();
            dstObjAccInfo->fieldSet[i]->belonging = dstObjAccInfo;
        }
        unionObjectFieldInfo(dstObjAccInfo->fieldSet[i], srcObjAccInfo->fieldSet[i], addrMap);
    }
}

static void createMatchTrack(ObjectAccInfo* srcTrackObj, std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap) {
    // indicates that in the iput, only the vdst is in the interest, we make a new corresponding object
    ObjectAccInfo* newAccInfo = new ObjectAccInfo();
    (*addrMap)[srcTrackObj] = newAccInfo;
    if(srcTrackObj->allFlag) {
        newAccInfo->allFlag = true;
    }
    if(srcTrackObj->inArray) {
        newAccInfo->inArray = true;
    }
    newAccInfo->fieldSet.resize(srcTrackObj->fieldSet.size());
    newAccInfo->trackSet.resize(srcTrackObj->trackSet.size());
    for(unsigned int i = 0; i < newAccInfo->trackSet.size(); i++) {
        if(srcTrackObj->trackSet[i] == NULL) {
            continue;
        }
        newAccInfo->trackSet[i] = new std::set<ObjectAccInfo*>();
        for(std::set<ObjectAccInfo*>::iterator it = srcTrackObj->trackSet[i]->begin(); it != srcTrackObj->trackSet[i]->end(); ++it) {
            if((*addrMap)[*it] == NULL) {
                createMatchTrack(*it, addrMap);
            }
            newAccInfo->trackSet[i]->insert((*addrMap)[*it]);
        }
    }
}

static void unionObjectTrackInfo(ObjectAccInfo* dstObjAccInfo, ObjectAccInfo* srcObjAccInfo, std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap) {
    for(unsigned int i = 0; i < srcObjAccInfo->trackSet.size(); i++) {
        if(dstObjAccInfo->fieldSet[i] != NULL && srcObjAccInfo->fieldSet[i] != NULL) {
            unionObjectTrackInfo(dstObjAccInfo->fieldSet[i], srcObjAccInfo->fieldSet[i], addrMap);
        }
        if(srcObjAccInfo->trackSet[i] == NULL || srcObjAccInfo->trackSet[i]->size() == 0) {
            continue;
        }
        if(dstObjAccInfo->trackSet[i] == NULL) {
            dstObjAccInfo->trackSet[i] = new std::set<ObjectAccInfo*>();
        }
        for(std::set<ObjectAccInfo*>::iterator it = srcObjAccInfo->trackSet[i]->begin(); it != srcObjAccInfo->trackSet[i]->end(); ++it) {
            if((*addrMap)[*it] == NULL) {
                createMatchTrack(*it, addrMap);
            }
            dstObjAccInfo->trackSet[i]->insert((*addrMap)[*it]);
        }
        //if(dstObjAccInfo->trackSet[i]->size() > 100) {
        //    ALOGE("union track get a large size: %u, the src size is: %u", dstObjAccInfo->trackSet[i]->size(), srcObjAccInfo->trackSet[i]->size());
        //}
    }
}

static void unionClazzFieldInfo(MethodAccInfo* dstAccInfo, MethodAccInfo* srcAccInfo, std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap) {
    for(unsigned int i = 0; i < srcAccInfo->globalClazz->size(); i++) {
        unsigned int j;
        for(j = 0; j < dstAccInfo->globalClazz->size(); j++) {
            if(srcAccInfo->globalClazz->at(i)->clazz == dstAccInfo->globalClazz->at(j)->clazz) {
                break;
            }
        }
        if(j == dstAccInfo->globalClazz->size()) {
            dstAccInfo->globalClazz->push_back(new ClazzAccInfo());
            dstAccInfo->globalClazz->at(j)->clazz = srcAccInfo->globalClazz->at(i)->clazz;
        }
        unionObjectFieldInfo(dstAccInfo->globalClazz->at(j), srcAccInfo->globalClazz->at(i), addrMap);
    }
}

static void unionClazzTrackInfo(MethodAccInfo* dstAccInfo, MethodAccInfo* srcAccInfo, std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap) {
    for(unsigned int i = 0; i < srcAccInfo->globalClazz->size(); i++) {
        unsigned int j;
        for(j = 0; j < dstAccInfo->globalClazz->size(); j++) {
            if(srcAccInfo->globalClazz->at(i)->clazz == dstAccInfo->globalClazz->at(j)->clazz) {
                break;
            }
        }
        unionObjectTrackInfo(dstAccInfo->globalClazz->at(j), srcAccInfo->globalClazz->at(i), addrMap);
    }
}

static void unionReturnObjs(MethodAccInfo* dstAccInfo, MethodAccInfo* srcAccInfo, std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap) {
    if(srcAccInfo->returnObjs == NULL || srcAccInfo->returnObjs->size() == 0) {
        return;
    }
    if(dstAccInfo->returnObjs == NULL) {
        dstAccInfo->returnObjs = new std::set<ObjectAccInfo*>();
    }
    for(std::set<ObjectAccInfo*>::iterator it = srcAccInfo->returnObjs->begin(); it != srcAccInfo->returnObjs->end(); ++it) {
        dstAccInfo->returnObjs->insert((*addrMap)[*it]);
    }
}

/* Union the two method access info into the dstAccInfo */
static void unionMethodAccInfo(MethodAccInfo* dstAccInfo, MethodAccInfo* srcAccInfo) {
    //ALOGE("union method info: %p - %s.%s, sub method is: %p - %s.%s", dstAccInfo->method, dstAccInfo->method->clazz->descriptor, dstAccInfo->method->name, srcAccInfo->method, srcAccInfo->method->clazz->descriptor, srcAccInfo->method->name);
    std::map<ObjectAccInfo*, ObjectAccInfo*> addrMap;
    // union the field access info for each args
    for(unsigned int i = 0; i < srcAccInfo->args->size(); i++) {
        unionObjectFieldInfo(dstAccInfo->args->at(i), srcAccInfo->args->at(i), &addrMap);
    }
    // union the class field access info for each class
    unionClazzFieldInfo(dstAccInfo, srcAccInfo, &addrMap);
    // union the field track info for each args
    for(unsigned int i = 0; i < srcAccInfo->args->size(); i++) {
        unionObjectTrackInfo(dstAccInfo->args->at(i), srcAccInfo->args->at(i), &addrMap);
    }
    // union the class field track info for each class
    unionClazzTrackInfo(dstAccInfo, srcAccInfo, &addrMap);
    // union the return objects
    unionReturnObjs(dstAccInfo, srcAccInfo, &addrMap);
}

static void mergeObjectAccFieldInfo(std::set<ObjectAccInfo*>* dstAccInfoList, ObjectAccInfo* srcAccInfo, std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap) {
    (*addrMap)[srcAccInfo] = *dstAccInfoList;
    if(srcAccInfo->inArray) {
        flagVecAllArray(dstAccInfoList);
    } else {
        if(srcAccInfo->allFlag) {
            flagVecAll(dstAccInfoList);
        }    
    }
    for(std::set<ObjectAccInfo*>::iterator it = dstAccInfoList->begin(); it != dstAccInfoList->end(); ++it) {
        if((*it)->fieldSet.size() < srcAccInfo->fieldSet.size()) {
            (*it)->fieldSet.resize(srcAccInfo->fieldSet.size());
            (*it)->trackSet.resize(srcAccInfo->trackSet.size());
        }
    }
    for(unsigned int i = 0; i < srcAccInfo->fieldSet.size(); i++) {
        if(srcAccInfo->fieldSet[i] == NULL) {
            continue;
        }
        std::set<ObjectAccInfo*> fieldList;
        for(std::set<ObjectAccInfo*>::iterator it = dstAccInfoList->begin(); it != dstAccInfoList->end(); ++it) {
            if((*it)->trackSet[i] == NULL) { // indicates that the field accessed is the original field
                (*it)->fieldSet[i] = new ObjectAccInfo();
                (*it)->fieldSet[i]->belonging = *it;
                (*it)->trackSet[i] = new std::set<ObjectAccInfo*>();
                (*it)->trackSet[i]->insert((*it)->fieldSet[i]);
                fieldList.insert((*it)->fieldSet[i]);
            } else {
                fieldList.insert((*it)->trackSet[i]->begin(), (*it)->trackSet[i]->end());
            }
        }
        mergeObjectAccFieldInfo(&fieldList, srcAccInfo->fieldSet[i], addrMap);
    }
}

void mergeObjectAccTrackInfo(std::set<ObjectAccInfo*>* dstAccInfoList, ObjectAccInfo* srcAccInfo, std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap, std::map<ObjectAccInfo*, ObjectAccInfo*>* changeCache);

static void createVecMatchTrack(ObjectAccInfo* srcTrackObj, std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap) {
    // indicates that in the iput, only the vdst is in the interest, we make a new corresponding object
    std::set<ObjectAccInfo*> result;
    ObjectAccInfo* newAccInfo = new ObjectAccInfo();
    result.insert(newAccInfo);
    (*addrMap)[srcTrackObj] = result;
    if(srcTrackObj->allFlag) {
        newAccInfo->allFlag = true;
    }
    if(srcTrackObj->inArray) {
        newAccInfo->inArray = true;
    }
    newAccInfo->fieldSet.resize(srcTrackObj->fieldSet.size());
    newAccInfo->trackSet.resize(srcTrackObj->trackSet.size());
    newAccInfo->mergeSet.resize(srcTrackObj->trackSet.size());
    for(unsigned int i = 0; i < newAccInfo->trackSet.size(); i++) {
        if(srcTrackObj->trackSet[i] == NULL) {
            continue;
        }
        newAccInfo->trackSet[i] = new std::set<ObjectAccInfo*>();
        for(std::set<ObjectAccInfo*>::iterator it = srcTrackObj->trackSet[i]->begin(); it != srcTrackObj->trackSet[i]->end(); ++it) {
            if((*addrMap).find(*it) == (*addrMap).end()) {
                createVecMatchTrack(*it, addrMap);
            }
            newAccInfo->trackSet[i]->insert((*addrMap)[*it].begin(), (*addrMap)[*it].end());
        }
    }
}

static void mergeObjectTrack(ObjectAccInfo* dstAccInfo, ObjectAccInfo* srcAccInfo, std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap, std::map<ObjectAccInfo*, ObjectAccInfo*>* changeCache) {
    //pushSingle(changeCache, dstAccInfo);
    if(changeCache->find(dstAccInfo) != changeCache->end()) {
        (*changeCache)[dstAccInfo] = dstAccInfo;
    }
    if(dstAccInfo->mergeSet.size() < dstAccInfo->trackSet.size()) {
        dstAccInfo->mergeSet.resize(dstAccInfo->trackSet.size());
    }
    for(unsigned int i = 0; i < srcAccInfo->trackSet.size(); i++) {
        if(srcAccInfo->fieldSet[i] != NULL) {
            mergeObjectAccTrackInfo(dstAccInfo->trackSet[i], srcAccInfo->fieldSet[i], addrMap, changeCache);
        }
        if(srcAccInfo->trackSet[i] == NULL || srcAccInfo->trackSet[i]->size() == 0) {
            continue;
        }
        if(srcAccInfo->trackSet[i]->size() == 1 && srcAccInfo->trackSet[i]->find(srcAccInfo->fieldSet[i]) != srcAccInfo->trackSet[i]->end()) {
            // indicates that the one in the track should not change, there is no assign to the track
            if(dstAccInfo->trackSet[i] == NULL) {
                dstAccInfo->trackSet[i] = new std::set<ObjectAccInfo*>();
                dstAccInfo->trackSet[i]->insert(dstAccInfo->fieldSet[i]);
            }
            if(dstAccInfo->mergeSet[i] == NULL) {
                dstAccInfo->mergeSet[i] = new std::set<ObjectAccInfo*>();
            }
            dstAccInfo->mergeSet[i]->insert(dstAccInfo->trackSet[i]->begin(), dstAccInfo->trackSet[i]->end());
            continue;
        }
        if(dstAccInfo->mergeSet[i] == NULL) {
            dstAccInfo->mergeSet[i] = new std::set<ObjectAccInfo*>();
        }
        for(std::set<ObjectAccInfo*>::iterator it = srcAccInfo->trackSet[i]->begin(); it != srcAccInfo->trackSet[i]->end(); ++it) {
            if((*addrMap).find(*it) == (*addrMap).end()) {
                createVecMatchTrack(*it, addrMap);
            }
            dstAccInfo->mergeSet[i]->insert((*addrMap)[*it].begin(), (*addrMap)[*it].end());
        }
    }
}

void mergeObjectAccTrackInfo(std::set<ObjectAccInfo*>* dstAccInfoList, ObjectAccInfo* srcAccInfo, std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap, std::map<ObjectAccInfo*, ObjectAccInfo*>* changeCache) {
    for(std::set<ObjectAccInfo*>::iterator it = dstAccInfoList->begin(); it != dstAccInfoList->end(); ++it) {
        mergeObjectTrack(*it, srcAccInfo, addrMap, changeCache);
    }
}

static void mergeGlobalClazzField(MethodAccInfo* methodAccInfo, MethodAccInfo* subAccInfo, std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap) {
    for(unsigned int i = 0; i < subAccInfo->globalClazz->size(); i++) {
        unsigned int j;
        for(j = 0; j < methodAccInfo->globalClazz->size(); j++) {
            if(subAccInfo->globalClazz->at(i)->clazz == methodAccInfo->globalClazz->at(j)->clazz) {
                break;
            }
        }
        if(j == methodAccInfo->globalClazz->size()) {
            methodAccInfo->globalClazz->push_back(new ClazzAccInfo());
            methodAccInfo->globalClazz->at(j)->clazz = subAccInfo->globalClazz->at(i)->clazz;
        }
        std::set<ObjectAccInfo*> argVec;
        argVec.insert(methodAccInfo->globalClazz->at(j));
        mergeObjectAccFieldInfo(&argVec, subAccInfo->globalClazz->at(i), addrMap);
    }
}

static void mergeGlobalClazzTrack(MethodAccInfo* methodAccInfo, MethodAccInfo* subAccInfo, std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap, std::map<ObjectAccInfo*, ObjectAccInfo*>* changeCache) {
    for(unsigned int i = 0; i < subAccInfo->globalClazz->size(); i++) {
        unsigned int j;
        for(j = 0; j < methodAccInfo->globalClazz->size(); j++) {
            if(subAccInfo->globalClazz->at(i)->clazz == methodAccInfo->globalClazz->at(j)->clazz) {
                break;
            }
        }
        mergeObjectTrack(methodAccInfo->globalClazz->at(j), subAccInfo->globalClazz->at(i), addrMap, changeCache);
    }
}

static void mergeMethodReturnInfo(MethodAccInfo* methodAccInfo, MethodAccInfo* subAccInfo, std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap) {
    if(subAccInfo->returnObjs == NULL || subAccInfo->returnObjs->size() == 0) {
        return;
    }
    methodAccInfo->curMethodReturns = new std::set<ObjectAccInfo*>();
    for(std::set<ObjectAccInfo*>::iterator it = subAccInfo->returnObjs->begin(); it != subAccInfo->returnObjs->end(); ++it) {
        methodAccInfo->curMethodReturns->insert(((*addrMap)[*it]).begin(), ((*addrMap)[*it]).end());
    }
}

/* check if the registers of the method are in our interest */
static bool methodHasInterest(u2 vsrc1, u2 vdst, std::map<u2, std::set<ObjectAccInfo*> >* interestRegObjMap) {
    u4 count = vsrc1 >> 4;
    u2 reg;
    bool hasInterest = false;
    switch (count) {
    case 5:
        reg = vsrc1 & 0x0f;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end() && !isVecFlagedAll(&((*interestRegObjMap)[reg]))) {
            hasInterest = true;
            break;
        }
    case 4:
        reg = vdst >> 12;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end() && !isVecFlagedAll(&((*interestRegObjMap)[reg]))) {
            hasInterest = true;
            break;
        }
    case 3:
        reg = (vdst & 0x0f00) >> 8;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end() && !isVecFlagedAll(&((*interestRegObjMap)[reg]))) {
            hasInterest = true;
            break;
        }
    case 2:
        reg = (vdst & 0x00f0) >> 4;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end() && !isVecFlagedAll(&((*interestRegObjMap)[reg]))) {
            hasInterest = true;
            break;
        }
    case 1:
        reg = vdst & 0x0f;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end() && !isVecFlagedAll(&((*interestRegObjMap)[reg]))) {
            hasInterest = true;
            break;
        }
    default:
        ;
    }
    return hasInterest;
}

/* flag the interest registers of the method as migrating all */
static void methodRegsFlagAll(u2 vsrc1, u2 vdst, std::map<u2, std::set<ObjectAccInfo*> >* interestRegObjMap) {
    u4 count = vsrc1 >> 4;
    u2 reg;
    switch (count) {
    case 5:
        reg = vsrc1 & 0x0f;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            flagVecAll(&((*interestRegObjMap)[reg]));
        }
    case 4:
        reg = vdst >> 12;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            flagVecAll(&((*interestRegObjMap)[reg]));
        }
    case 3:
        reg = (vdst & 0x0f00) >> 8;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            flagVecAll(&((*interestRegObjMap)[reg]));
        }
    case 2:
        reg = (vdst & 0x00f0) >> 4;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            flagVecAll(&((*interestRegObjMap)[reg]));
        }
    case 1:
        reg = vdst & 0x0f;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            flagVecAll(&((*interestRegObjMap)[reg]));
        }
    default:
        ;
    }
}

static void applyMergeToTrack(std::map<ObjectAccInfo*, ObjectAccInfo*>* changeCache) {
    for (std::map<ObjectAccInfo*, ObjectAccInfo*>::iterator it = changeCache->begin(); it != changeCache->end(); ++it) {
        ObjectAccInfo* objAccInfo = it->second;
        if(objAccInfo->mergeSet.size() == 0) {
            // indicates we have processed this obj in previous iteration
            continue;
        }
        assert(objAccInfo->mergeSet.size() == objAccInfo->trackSet.size());
        for(unsigned int j = 0; j < objAccInfo->trackSet.size(); j++) {
            if(objAccInfo->trackSet[j] != NULL) {
                delete objAccInfo->trackSet[j];
            }
            objAccInfo->trackSet[j] = objAccInfo->mergeSet[j];
            objAccInfo->mergeSet[j] = NULL;
        }
        objAccInfo->mergeSet.clear();
    }
}

/* populate the args info for the method */
static void mergeMethodArgs(u2 vsrc1, u2 vdst, std::map<u2, std::set<ObjectAccInfo*> >* interestRegObjMap, MethodAccInfo* methodAccInfo, MethodAccInfo* subAccInfo) {
    u4 count = vsrc1 >> 4;
    u2 reg;
    std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> > addrMap;
    switch (count) {
    case 5:
        reg = vsrc1 & 0x0f;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccFieldInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(4), &addrMap);
        }
    case 4:
        reg = vdst >> 12;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccFieldInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(3), &addrMap);
        }
    case 3:
        reg = (vdst & 0x0f00) >> 8;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccFieldInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(2), &addrMap);
        }
    case 2:
        reg = (vdst & 0x00f0) >> 4;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccFieldInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(1), &addrMap);
        }
    case 1:
        reg = vdst & 0x0f;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccFieldInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(0), &addrMap);
        }
    default:
        ;
    }
    // merge global field info
    mergeGlobalClazzField(methodAccInfo, subAccInfo, &addrMap);
    std::map<ObjectAccInfo*, ObjectAccInfo*>* changeCache = new std::map<ObjectAccInfo*, ObjectAccInfo*>();
    switch (count) {
    case 5:
        reg = vsrc1 & 0x0f;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccTrackInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(4), &addrMap, changeCache);
        }
    case 4:
        reg = vdst >> 12;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccTrackInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(3), &addrMap, changeCache);
        }
    case 3:
        reg = (vdst & 0x0f00) >> 8;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccTrackInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(2), &addrMap, changeCache);
        }
    case 2:
        reg = (vdst & 0x00f0) >> 4;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccTrackInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(1), &addrMap, changeCache);
        }
    case 1:
        reg = vdst & 0x0f;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccTrackInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(0), &addrMap, changeCache);
        }
    default:
        ;
    }
    // merge global track info
    mergeGlobalClazzTrack(methodAccInfo, subAccInfo, &addrMap, changeCache);
    applyMergeToTrack(changeCache);
    delete changeCache;
    mergeMethodReturnInfo(methodAccInfo, subAccInfo, &addrMap);
}

/* check if the registers of the range method are in our interest */
static bool rangeMethodHasInterest(u2 vsrc1, u2 vdst, std::map<u2, std::set<ObjectAccInfo*> >* interestRegObjMap) {
    bool hasInterest = false;
    for(int i = 0; i < vsrc1; i++) {
        if(interestRegObjMap->find(vdst + i) != interestRegObjMap->end() && !isVecFlagedAll(&((*interestRegObjMap)[vdst + i]))) {
            hasInterest = true;
            break;
        }
    }
    return hasInterest;
}

/* flag the interest registers of the range method as migrating all */
static void rangeMethodRegsFlagAll(u2 vsrc1, u2 vdst, std::map<u2, std::set<ObjectAccInfo*> >* interestRegObjMap) {
    for(int i = 0; i < vsrc1; i++) {
        if(interestRegObjMap->find(vdst + i) != interestRegObjMap->end()) {
            flagVecAll(&((*interestRegObjMap)[vdst + i]));
        }
    }
}

/* populate the args info for the method */
static void mergeRangeMethodArgs(u2 vsrc1, u2 vdst, std::map<u2, std::set<ObjectAccInfo*> >* interestRegObjMap, MethodAccInfo* methodAccInfo, MethodAccInfo* subAccInfo) {
    std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> > addrMap;
    for(int i = 0; i < vsrc1; i++) {
        if(interestRegObjMap->find(vdst + i) != interestRegObjMap->end()) {
            mergeObjectAccFieldInfo(&((*interestRegObjMap)[vdst + i]), subAccInfo->args->at(i), &addrMap);
        }
    }
    // merge global field info
    mergeGlobalClazzField(methodAccInfo, subAccInfo, &addrMap);
    std::map<ObjectAccInfo*, ObjectAccInfo*>* changeCache = new std::map<ObjectAccInfo*, ObjectAccInfo*>();
    for(int i = 0; i < vsrc1; i++) {
        if(interestRegObjMap->find(vdst + i) != interestRegObjMap->end()) {
            mergeObjectAccTrackInfo(&((*interestRegObjMap)[vdst + i]), subAccInfo->args->at(i), &addrMap, changeCache);
        }
    }
    // merge global track info
    mergeGlobalClazzTrack(methodAccInfo, subAccInfo, &addrMap, changeCache);
    applyMergeToTrack(changeCache);
    delete changeCache;
    mergeMethodReturnInfo(methodAccInfo, subAccInfo, &addrMap);
}

/*void handleLoop(const u2* insns, MethodAccInfo* methodAccInfo, std::vector<int>* insOffsets, int startIdx, std::map<u2, std::vector<ObjectAccInfo*> >* interestRegObjMap) {
    
}*/

static void handleCatchBranch(const u2* insns, MethodAccInfo* methodAccInfo, std::set<Method*>* chain, std::vector<int>* insOffsets, std::map<u2, std::set<ObjectAccInfo*> >* interestRegObjMap, int depth, bool* exitMethod) {
    Method* method = methodAccInfo->method;
    int relPc = insns - method->insns;
    const DexCode* pCode = dvmGetMethodCode(method);
    DexCatchIterator iterator;

    if (dexFindCatchHandler(&iterator, pCode, relPc)) {
        for (;;) {
            DexCatchHandler* handler = dexCatchIteratorNext(&iterator);

            if (handler == NULL) {
                break;
            }
            int catchOffset = handler->address;
            // check if the switch case will lead to an instruction cycle
            bool isCycle = false;
            for(unsigned int i = 0; i < insOffsets->size(); i++) {
                if(catchOffset == insOffsets->at(i)) {
                    isCycle = true;
                    break;
                }
            }
            if(!isCycle) {
                // parse the branch taken
                const u2* temp = method->insns;
                temp += catchOffset;
                std::vector<int> tempInsOffsets = *insOffsets;
                std::map<u2, std::set<ObjectAccInfo*> > tempInterest = *interestRegObjMap;
                int newDepth = depth + 1;
                // If we reach the maximum branch depth, we exit the parse of the method to save the cost of parse
                if(newDepth >= MaxBranchDepth) {
                    for(unsigned int i = 0; i < methodAccInfo->args->size(); i++) {
                        flagObjAll(methodAccInfo->args->at(i));
                    }
                    *exitMethod = true;
                    return;
                }
                parseInsns(temp, methodAccInfo, chain, &tempInsOffsets, &tempInterest, newDepth, exitMethod);
            }
        }
    }
}

void parseInsns(const u2* insns, MethodAccInfo* methodAccInfo, std::set<Method*>* chain, std::vector<int>* insOffsets, std::map<u2, std::set<ObjectAccInfo*> >* interestRegObjMap, int depth, bool* exitMethod) {
    if(*exitMethod) {
        return;
    }
    Method* method = methodAccInfo->method;
    DvmDex* methodClassDex = method->clazz->pDvmDex;
    u2 vsrc1, vdst;
    u4 ref;
    Opcode opcode, lastOpcode = OP_UNUSED_79;
    int width, currentOffset;
    for( ; ; lastOpcode = opcode, insns += width) {
        width = dexGetWidthFromInstruction(insns);
        opcode = dexOpcodeFromCodeUnit(*insns);
        currentOffset = insns - method->insns;
        insOffsets->push_back(currentOffset);
        // each instruction might raise an exception, go to the corresponding handler to process
        handleCatchBranch(insns, methodAccInfo, chain, insOffsets, interestRegObjMap, depth, exitMethod);
        if(*exitMethod) {
            return;
        }
        if(opcode == OP_IGET || opcode == OP_IGET_WIDE || opcode == OP_IGET_OBJECT || opcode == OP_IGET_BOOLEAN 
            || opcode == OP_IGET_BYTE || opcode == OP_IGET_CHAR || opcode == OP_IGET_SHORT 
            || opcode == OP_IGET_VOLATILE || opcode == OP_IGET_OBJECT_VOLATILE || opcode == OP_IGET_WIDE_VOLATILE) {
            vdst = inst_a(insns);
            vsrc1 = inst_b(insns);
            // check if the source register is in our interest list
            if(interestRegObjMap->find(vsrc1) == interestRegObjMap->end()) {
                // erase to initiate
                interestRegObjMap->erase(vdst);
                continue;
            }
            ref = insns[1];
            unsigned int offset;
            InstField* ifield = (InstField*) dvmDexGetResolvedField(methodClassDex, ref); 
            if (ifield == NULL) {
                ifield = resolveInstField(method->clazz, ref);
                if(ifield == NULL) { // we should have encountered a wrong version field branch
                    return;
                }
            }
            offset = (ifield->byteOffset - sizeof(Object)) >> 2;
            
            // set the field of the object as accessed
            std::set<ObjectAccInfo*> accVector = (*interestRegObjMap)[vsrc1];
            interestRegObjMap->erase(vdst);
            for(std::set<ObjectAccInfo*>::iterator it = accVector.begin(); it != accVector.end(); ++it) {
                ObjectAccInfo* objAccInfo = *it;
                assert(objAccInfo != NULL);
                // the current size are not big enough, it means that the field is not set by other instruction and its access is to the field of the object
                if(objAccInfo->trackSet.size() < offset + 1) {
                    // resize the vector to accomodate the offset
                    objAccInfo->fieldSet.resize(offset + 1);
                    objAccInfo->trackSet.resize(offset + 1);
                }
                // if the field has not been setup, then set the field
                if(objAccInfo->trackSet[offset] == NULL) {
                    ObjectAccInfo* fieldInfo = new ObjectAccInfo();
                    fieldInfo->belonging = objAccInfo;
                    if(objAccInfo->inArray) {
                        fieldInfo->inArray = true;
                    }
                    objAccInfo->fieldSet[offset] = fieldInfo;
                    objAccInfo->trackSet[offset] = new std::set<ObjectAccInfo*>();
                    objAccInfo->trackSet[offset]->insert(objAccInfo->fieldSet[offset]);
                }
                if(opcode == OP_IGET_OBJECT || opcode == OP_IGET_OBJECT_VOLATILE) {
                    ((*interestRegObjMap)[vdst]).insert(objAccInfo->trackSet[offset]->begin(), objAccInfo->trackSet[offset]->end());
                }
            }
        } else if(opcode == OP_IPUT_OBJECT || opcode == OP_IPUT_OBJECT_VOLATILE) { // if the dst is in the interest, the src object's field should also be in interest
            vdst = inst_a(insns);
            vsrc1 = inst_b(insns);   
            ref = insns[1];   
            unsigned int offset;
            InstField* ifield = (InstField*) dvmDexGetResolvedField(methodClassDex, ref); 
            if (ifield == NULL) {
                ifield = resolveInstField(method->clazz, ref);
                if(ifield == NULL) { // we should have encountered a wrong version field branch
                    return;
                }
            }
            offset = (ifield->byteOffset - sizeof(Object)) >> 2;
            
            // both src object and dst are not in our interest
            if(interestRegObjMap->find(vdst) == interestRegObjMap->end() && interestRegObjMap->find(vsrc1) == interestRegObjMap->end()) {
                continue;
            } else if(interestRegObjMap->find(vdst) == interestRegObjMap->end() && interestRegObjMap->find(vsrc1) != interestRegObjMap->end()) { 
                // only src object are in interest, in this case, we set the offset to be an arbitrary one to make sure it will not pollute the original data
                std::set<ObjectAccInfo*> srcVector = (*interestRegObjMap)[vsrc1];
                for(std::set<ObjectAccInfo*>::iterator it = srcVector.begin(); it != srcVector.end(); ++it) {
                    ObjectAccInfo* interestAccInfo = *it;
                    if(interestAccInfo->trackSet.size() < offset + 1) {
                        interestAccInfo->fieldSet.resize(offset + 1);
                        interestAccInfo->trackSet.resize(offset + 1);
                    }
                    if(interestAccInfo->trackSet[offset] != NULL) {
                        delete interestAccInfo->trackSet[offset];
                    }
                    interestAccInfo->trackSet[offset] = new std::set<ObjectAccInfo*>();
                }
                continue;
            }
            // the dst register is in our interest
            if(interestRegObjMap->find(vsrc1) == interestRegObjMap->end()) {
                (*interestRegObjMap)[vsrc1].insert(new ObjectAccInfo());
            }
                    
            std::set<ObjectAccInfo*> srcVector = (*interestRegObjMap)[vsrc1];
            bool hasInArray = false;
            for(std::set<ObjectAccInfo*>::iterator it = srcVector.begin(); it != srcVector.end(); ++it) {
                ObjectAccInfo* interestAccInfo = *it;
                if(!hasInArray && interestAccInfo->inArray) {
                    hasInArray = true;
                    flagVecAllArray(&((*interestRegObjMap)[vdst]));
                }
                if(interestAccInfo->trackSet.size() < offset + 1) {
                    interestAccInfo->fieldSet.resize(offset + 1);
                    interestAccInfo->trackSet.resize(offset + 1);
                }
                if(interestAccInfo->trackSet[offset] != NULL) {
                    delete interestAccInfo->trackSet[offset];
                }
                interestAccInfo->trackSet[offset] = new std::set<ObjectAccInfo*>();
                interestAccInfo->trackSet[offset]->insert((*interestRegObjMap)[vdst].begin(), (*interestRegObjMap)[vdst].end());
            }
        } else if(opcode == OP_SGET_VOLATILE || opcode == OP_SGET_WIDE_VOLATILE || opcode == OP_SGET_OBJECT_VOLATILE
            || opcode == OP_SGET || opcode == OP_SGET_WIDE || opcode == OP_SGET_OBJECT || opcode == OP_SGET_BOOLEAN
            || opcode == OP_SGET_BYTE || opcode == OP_SGET_CHAR || opcode == OP_SGET_SHORT) {
            vdst = inst_a(insns);
            ref = insns[1];
            StaticField* sfield = (StaticField*)dvmDexGetResolvedField(methodClassDex, ref);
            if (sfield == NULL) {
                sfield = resolveStaticField(method->clazz, ref);
                if(sfield == NULL) { // we should have encountered a wrong version field branch
                    return;
                }
            }
            unsigned int offset = sfield - sfield->clazz->sfields;
            unsigned int i;
            for(i = 0; i < methodAccInfo->globalClazz->size(); i++) {
                if(sfield->clazz == methodAccInfo->globalClazz->at(i)->clazz) {
                    break;
                }
            }
            if(i == methodAccInfo->globalClazz->size()) { // The first time to deal this global class object
                ClazzAccInfo* clazzAccInfo = new ClazzAccInfo();
                clazzAccInfo->clazz = sfield->clazz;
                methodAccInfo->globalClazz->push_back(clazzAccInfo);
            }
            ClazzAccInfo* clazzAccInfo = methodAccInfo->globalClazz->at(i);
            if(clazzAccInfo->trackSet.size() < offset + 1) { // the current size of trackSet vector are not big enough
                clazzAccInfo->fieldSet.resize(offset + 1);
                clazzAccInfo->trackSet.resize(offset + 1);
            }
            // if the field has not been setup, then set the field
            if(clazzAccInfo->trackSet[offset] == NULL) {
                ObjectAccInfo* fieldInfo = new ObjectAccInfo();
                fieldInfo->belonging = clazzAccInfo;
                if(clazzAccInfo->inArray) {
                    fieldInfo->inArray = true;
                }
                clazzAccInfo->fieldSet[offset] = fieldInfo;
                clazzAccInfo->trackSet[offset] = new std::set<ObjectAccInfo*>();
                clazzAccInfo->trackSet[offset]->insert(clazzAccInfo->fieldSet[offset]);
            }
            interestRegObjMap->erase(vdst);
            // if the object is already set as migrate all, then ignore it
            //if(isVecFlagedAll(clazzAccInfo->trackSet[offset])) {
            //    continue;
            //}
            // add the destination register into the interest map
            if(opcode == OP_SGET_OBJECT_VOLATILE || opcode == OP_SGET_OBJECT) {
                (*interestRegObjMap)[vdst] = *(clazzAccInfo->trackSet[offset]);
            }
        } else if(opcode == OP_SPUT_OBJECT || opcode == OP_SPUT_OBJECT_VOLATILE) {// if the dst is in the interest, the src class'es field should also be in interest
            vdst = inst_aa(insns);
            ref = insns[1];  
            StaticField* sfield = (StaticField*)dvmDexGetResolvedField(methodClassDex, ref);
            if (sfield == NULL) {
                sfield = resolveStaticField(method->clazz, ref);
                if(sfield == NULL) { // we should have encountered a wrong version field branch
                    return;
                }
            }
            unsigned int offset = sfield - sfield->clazz->sfields;
            unsigned int i;
            for(i = 0; i < methodAccInfo->globalClazz->size(); i++) {
                if(sfield->clazz == methodAccInfo->globalClazz->at(i)->clazz) {
                    break;
                }
            }
            if(i == methodAccInfo->globalClazz->size()) { // The first time to deal this global class object
                ClazzAccInfo* clazzAccInfo = new ClazzAccInfo();
                clazzAccInfo->clazz = sfield->clazz;
                methodAccInfo->globalClazz->push_back(clazzAccInfo);
            }
            ClazzAccInfo* clazzAccInfo = methodAccInfo->globalClazz->at(i);
            if(clazzAccInfo->trackSet.size() < offset + 1) { // the current size of trackSet vector are not big enough
                clazzAccInfo->fieldSet.resize(offset + 1);
                clazzAccInfo->trackSet.resize(offset + 1);
            }
            // only src clazz are in interest, in this case, we set the offset to be an arbitrary one to make sure it will not pollute the original data
            if(interestRegObjMap->find(vdst) == interestRegObjMap->end()) {
                if(clazzAccInfo->trackSet[offset] != NULL) {
                    delete clazzAccInfo->trackSet[offset];
                }
                clazzAccInfo->trackSet[offset] = new std::set<ObjectAccInfo*>();
                continue;
            }
            // the src clazz and dst register are both in our interest
            if(clazzAccInfo->trackSet[offset] != NULL) {
                delete clazzAccInfo->trackSet[offset];
            }
            if(clazzAccInfo->inArray) {
                flagVecAllArray(&((*interestRegObjMap)[vdst]));
            }
            clazzAccInfo->trackSet[offset] = new std::set<ObjectAccInfo*>();
            clazzAccInfo->trackSet[offset]->insert((*interestRegObjMap)[vdst].begin(), (*interestRegObjMap)[vdst].end());
        } else if(opcode == OP_MOVE || opcode == OP_MOVE_FROM16 || opcode == OP_MOVE_16
            || opcode == OP_MOVE_WIDE || opcode == OP_MOVE_WIDE_FROM16 || opcode == OP_MOVE_WIDE_16
            || opcode == OP_MOVE_OBJECT || opcode == OP_MOVE_OBJECT_FROM16 || opcode == OP_MOVE_OBJECT_16) {
            if(opcode == OP_MOVE || opcode == OP_MOVE_WIDE || opcode == OP_MOVE_OBJECT) {
                vdst = inst_a(insns);
                vsrc1 = inst_b(insns);
            } else if(opcode == OP_MOVE_FROM16 || opcode == OP_MOVE_WIDE_FROM16 || opcode == OP_MOVE_OBJECT_FROM16) {
                vdst = inst_aa(insns);
                vsrc1 = insns[1];
            } else if(opcode == OP_MOVE_16 || opcode == OP_MOVE_WIDE_16 || opcode == OP_MOVE_OBJECT_16) {
                vdst = insns[1];
                vsrc1 = insns[2];
            }
            // check if the source register is in our interest list
            if(interestRegObjMap->find(vsrc1) == interestRegObjMap->end()) {
                // this attribute is not our interest, remove dst register from interest list
                interestRegObjMap->erase(vdst);
            } else {
                // add the destination register into the interest map
                (*interestRegObjMap)[vdst] = (*interestRegObjMap)[vsrc1];
            }
        } else if(opcode == OP_INVOKE_VIRTUAL || opcode == OP_INVOKE_VIRTUAL_RANGE) {
            vsrc1 = inst_aa(insns);      // AA (count) or BA (count + arg 5) 
            ref = insns[1];             // method ref 
            vdst = insns[2];            // 4 regs -or- first reg
            if(methodAccInfo->curMethodReturns != NULL) {
                delete methodAccInfo->curMethodReturns;
                methodAccInfo->curMethodReturns = NULL;
            }
            
            int voffset;
            Method* baseMethod;
            baseMethod = dvmDexGetResolvedMethod(methodClassDex, ref);
            if (baseMethod == NULL) {
                baseMethod = resolveMethod(method->clazz, ref, METHOD_VIRTUAL);
                if(baseMethod == NULL) { // we should have encountered a wrong version method branch
                    return;
                }
            }
            voffset = baseMethod->methodIndex;
            
            // check if the method invocation involves interesting registers
            bool hasInterest;
            if(opcode == OP_INVOKE_VIRTUAL) {
                hasInterest = methodHasInterest(vsrc1, vdst, interestRegObjMap);
            } else {
                hasInterest = rangeMethodHasInterest(vsrc1, vdst, interestRegObjMap);
            }
            if(!hasInterest) {
                continue;
            }
            
            bool isLangObjectClass = baseMethod->clazz == javaLangObject;
            bool isExempt = false;
            for(unsigned int idx = 0; idx < exemptClzs->size(); idx++) {
                if(baseMethod->clazz == exemptClzs->at(idx)) {
                    isExempt = true;
                    break;
                }
            }
            if(isLangObjectClass || isExempt) {
                if(opcode == OP_INVOKE_VIRTUAL) {
                    methodRegsFlagAll(vsrc1, vdst, interestRegObjMap);
                } else {
                    rangeMethodRegsFlagAll(vsrc1, vdst, interestRegObjMap);
                }
                continue;
            }
            //ALOGE("methodParser parse virtual %s.%s", baseMethod->clazz->descriptor, baseMethod->name);
            MethodAccInfo* subAccInfo;
            if(virtualResMap.find(baseMethod) != virtualResMap.end()) {
                subAccInfo = virtualResMap[baseMethod];
            } else {
                subAccInfo = new MethodAccInfo();
                subAccInfo->method = baseMethod;
                populateMethodAccInfo(subAccInfo);
                std::vector<ClassObject*>* subclasses = findSubClass(baseMethod->clazz);
                if(subclasses->size() > MaxSubCount) {
                    //ALOGE("method: %s.%s, size is: %u", baseMethod->clazz->descriptor, baseMethod->name, subclasses.size());
                    if(opcode == OP_INVOKE_VIRTUAL) {
                        methodRegsFlagAll(vsrc1, vdst, interestRegObjMap);
                    } else {
                        rangeMethodRegsFlagAll(vsrc1, vdst, interestRegObjMap);
                    }
                    continue;
                }
                // use this vector to store the method which have been parsed since it seems that the method which is not overriden by its subclass will have the same reference
                std::set<Method*> parsedMethod;
                
                for(unsigned int idx = 0; idx < subclasses->size(); idx++) {
                    Method* methodToCall = subclasses->at(idx)->vtable[voffset];
                    assert(methodToCall != NULL);
                    if(parsedMethod.find(methodToCall) != parsedMethod.end()) {
                        continue;
                    } else {
                        parsedMethod.insert(methodToCall);
                    }
                    MethodAccInfo* toCallAccInfo;
                    if(methodResMap.find(methodToCall) == methodResMap.end()) {
                        // setup subcall method access info and parse
                        toCallAccInfo = parseMethod(methodToCall, chain);
                    } else {
                        toCallAccInfo = methodResMap[methodToCall];
                    }
                    unionMethodAccInfo(subAccInfo, toCallAccInfo);
                }
                virtualResMap[baseMethod] = subAccInfo;
            }
            if(opcode == OP_INVOKE_VIRTUAL) {
                mergeMethodArgs(vsrc1, vdst, interestRegObjMap, methodAccInfo, subAccInfo);
            } else {
                mergeRangeMethodArgs(vsrc1, vdst, interestRegObjMap, methodAccInfo, subAccInfo);
            }
        } else if(opcode == OP_INVOKE_INTERFACE || opcode == OP_INVOKE_INTERFACE_RANGE) { // see Interp.cpp-dvmInterpFindInterfaceMethod
            vsrc1 = inst_aa(insns);      // AA (count) or BA (count + arg 5) 
            ref = insns[1];             // method ref 
            vdst = insns[2];            // 4 regs -or- first reg
            if(methodAccInfo->curMethodReturns != NULL) {
                delete methodAccInfo->curMethodReturns;
                methodAccInfo->curMethodReturns = NULL;
            }
            
            Method* absMethod;
            absMethod = dvmDexGetResolvedMethod(methodClassDex, ref);
            if (absMethod == NULL) {
                absMethod = resolveInterfaceMethod(method->clazz, ref);
                 if(absMethod == NULL) { // we should have encountered a wrong version method branch
                    return;
                }
            }
            assert(dvmIsAbstractMethod(absMethod));
            
            // check if the method invocation involves interesting registers
            bool hasInterest;
            if(opcode == OP_INVOKE_INTERFACE) {
                hasInterest = methodHasInterest(vsrc1, vdst, interestRegObjMap);
            } else {
                hasInterest = rangeMethodHasInterest(vsrc1, vdst, interestRegObjMap);
            }
            if(!hasInterest) {
                continue;
            }
            
            bool isExempt = false;
            for(unsigned int idx = 0; idx < exemptIfs->size(); idx++) {
                if(absMethod->clazz == exemptIfs->at(idx)) {
                    isExempt = true;
                    break;
                }
            }
            if(isExempt) {
                if(opcode == OP_INVOKE_INTERFACE) {
                    methodRegsFlagAll(vsrc1, vdst, interestRegObjMap);
                } else {
                    rangeMethodRegsFlagAll(vsrc1, vdst, interestRegObjMap);
                }
                continue;
            }
            
            //ALOGE("methodParser parse virtual %s.%s", baseMethod->clazz->descriptor, baseMethod->name);
            MethodAccInfo* subAccInfo;
            if(interResMap.find(absMethod) != interResMap.end()) {
                subAccInfo = interResMap[absMethod];
            } else {
                subAccInfo = new MethodAccInfo();
                subAccInfo->method = absMethod;
                populateMethodAccInfo(subAccInfo);
                std::vector<ClassObject*>* implclasses = findImplementClass(absMethod->clazz);
                if(implclasses->size() > MaxSubCount) {
                    //ALOGE("method: %s.%s, size is: %u", absMethod->clazz->descriptor, absMethod->name, implclasses.size());
                    if(opcode == OP_INVOKE_VIRTUAL) {
                        methodRegsFlagAll(vsrc1, vdst, interestRegObjMap);
                    } else {
                        rangeMethodRegsFlagAll(vsrc1, vdst, interestRegObjMap);
                    }
                    continue;
                }
                // use this vector to store the method which have been parsed since it seems that the method which is not overriden by its subclass will have the same reference
                std::set<Method*> parsedMethod;
                
                for(unsigned int idx = 0; idx < implclasses->size(); idx++) {
                    Method* methodToCall;
                    int ifIdx;
                    for (ifIdx = 0; ifIdx < implclasses->at(idx)->iftableCount; ifIdx++) {
                        if (implclasses->at(idx)->iftable[ifIdx].clazz == absMethod->clazz) {
                            break;
                        }
                    }
                    int vtableIndex = implclasses->at(idx)->iftable[ifIdx].methodIndexArray[absMethod->methodIndex];
                    methodToCall = implclasses->at(idx)->vtable[vtableIndex];
                    assert(methodToCall != NULL);
                    if(parsedMethod.find(methodToCall) != parsedMethod.end()) {
                        continue;
                    } else {
                        parsedMethod.insert(methodToCall);
                    }
                    MethodAccInfo* toCallAccInfo;
                    if(methodResMap.find(methodToCall) == methodResMap.end()) {
                        // setup subcall method access info and parse
                        toCallAccInfo = parseMethod(methodToCall, chain);
                    } else {
                        toCallAccInfo = methodResMap[methodToCall];
                    }
                    unionMethodAccInfo(subAccInfo, toCallAccInfo);
                }
                interResMap[absMethod] = subAccInfo;
            }
            if(opcode == OP_INVOKE_INTERFACE) {
                mergeMethodArgs(vsrc1, vdst, interestRegObjMap, methodAccInfo, subAccInfo);
            } else {
                mergeRangeMethodArgs(vsrc1, vdst, interestRegObjMap, methodAccInfo, subAccInfo);
            }
        } else if(opcode == OP_INVOKE_SUPER || opcode == OP_INVOKE_DIRECT || opcode == OP_INVOKE_STATIC 
            || opcode == OP_INVOKE_SUPER_RANGE || opcode == OP_INVOKE_DIRECT_RANGE || opcode == OP_INVOKE_STATIC_RANGE) {
            vsrc1 = inst_aa(insns);      // AA (count) or BA (count + arg 5) 
            ref = insns[1];             // method ref 
            vdst = insns[2];            // 4 regs -or- first reg
            if(methodAccInfo->curMethodReturns != NULL) {
                delete methodAccInfo->curMethodReturns; 
                methodAccInfo->curMethodReturns = NULL;
            }
            
            // check if the method invocation involves interesting registers
            bool hasInterest;
            if(opcode == OP_INVOKE_SUPER || opcode == OP_INVOKE_DIRECT || opcode == OP_INVOKE_STATIC) {
                hasInterest = methodHasInterest(vsrc1, vdst, interestRegObjMap);
            } else {
                hasInterest = rangeMethodHasInterest(vsrc1, vdst, interestRegObjMap);
            }
            if(!hasInterest) {
                continue;
            }
            
            Method* methodToCall;
            if(opcode == OP_INVOKE_SUPER || opcode == OP_INVOKE_SUPER_RANGE) {
                Method* baseMethod;
                baseMethod = dvmDexGetResolvedMethod(methodClassDex, ref);
                if (baseMethod == NULL) {
                    baseMethod = resolveMethod(method->clazz, ref, METHOD_VIRTUAL);
                    if(baseMethod == NULL) { // we should have encountered a wrong version method branch
                        return;
                    }
                }
                assert(baseMethod->methodIndex < method->clazz->super->vtableCount);
                methodToCall = method->clazz->super->vtable[baseMethod->methodIndex];
            } else if(opcode == OP_INVOKE_DIRECT || opcode == OP_INVOKE_DIRECT_RANGE) {
                methodToCall = dvmDexGetResolvedMethod(methodClassDex, ref);
                if (methodToCall == NULL) {
                    methodToCall = resolveMethod(method->clazz, ref, METHOD_DIRECT);
                }
            } else {
                methodToCall = dvmDexGetResolvedMethod(methodClassDex, ref);
                if (methodToCall == NULL) {
                    methodToCall = resolveMethod(method->clazz, ref, METHOD_STATIC);
                }
            } 
            if(methodToCall == NULL) { // we should have encountered a wrong version method branch
                return;
            }
            //ALOGE("methodParser parse virtual %s.%s", baseMethod->clazz->descriptor, baseMethod->name);
            MethodAccInfo* subAccInfo;
            if(methodResMap.find(methodToCall) == methodResMap.end()) {
                // setup subcall method access info and parse
                subAccInfo = parseMethod(methodToCall, chain);
            } else {
                subAccInfo = methodResMap[methodToCall];
            }
            if(opcode == OP_INVOKE_SUPER || opcode == OP_INVOKE_DIRECT || opcode == OP_INVOKE_STATIC) {
                mergeMethodArgs(vsrc1, vdst, interestRegObjMap, methodAccInfo, subAccInfo);
            } else {
                mergeRangeMethodArgs(vsrc1, vdst, interestRegObjMap, methodAccInfo, subAccInfo);
            }
        } else if(opcode == OP_MOVE_RESULT || opcode == OP_MOVE_RESULT_WIDE || opcode == OP_MOVE_EXCEPTION) {
            vdst = inst_aa(insns);
            interestRegObjMap->erase(vdst);
            if(methodAccInfo->curMethodReturns != NULL) {
                delete methodAccInfo->curMethodReturns;
                methodAccInfo->curMethodReturns = NULL;
            }
        } else if(opcode == OP_MOVE_RESULT_OBJECT) {
            vdst = inst_aa(insns);
            // we only process the move result of a method
            if(lastOpcode == OP_FILLED_NEW_ARRAY || lastOpcode == OP_FILLED_NEW_ARRAY_RANGE) {
                // in this case, we erase the destination register from the interest interest because we have flagged the object it include as all
                interestRegObjMap->erase(vdst);
                continue;
            }
            if(methodAccInfo->curMethodReturns != NULL) {
                (*interestRegObjMap)[vdst] = *(methodAccInfo->curMethodReturns);
                delete methodAccInfo->curMethodReturns;
                methodAccInfo->curMethodReturns = NULL;
            } else {
                interestRegObjMap->erase(vdst);
            }
        } else if(opcode == OP_RETURN_VOID || opcode == OP_RETURN || opcode == OP_RETURN_WIDE) {
            // stop the current branch of parsing instruction stream
            return;
        } else if(opcode == OP_RETURN_OBJECT) {
            vsrc1 = inst_aa(insns);
            if(interestRegObjMap->find(vsrc1) != interestRegObjMap->end()) {
                if(methodAccInfo->returnObjs == NULL) {
                    methodAccInfo->returnObjs = new std::set<ObjectAccInfo*>();
                }
                methodAccInfo->returnObjs->insert(((*interestRegObjMap)[vsrc1]).begin(), ((*interestRegObjMap)[vsrc1]).end());
            }
            // stop the current branch of parsing instruction stream
            return;
        } else if(opcode == OP_IF_EQ || opcode == OP_IF_NE || opcode == OP_IF_LT
            || opcode == OP_IF_GE || opcode == OP_IF_GT || opcode == OP_IF_LE
            || opcode == OP_IF_EQZ || opcode == OP_IF_NEZ || opcode == OP_IF_LTZ
            || opcode == OP_IF_GEZ || opcode == OP_IF_GTZ || opcode == OP_IF_LEZ) {
            int branchOffset = (s2)insns[1];
            // check if the branch will lead to an instruction cycle
            bool isCycle = false;
            int newOffset = currentOffset + branchOffset;
            for(unsigned int i = 0; i < insOffsets->size(); i++) {
                if(newOffset == insOffsets->at(i)) {
                    isCycle = true;
                    break;
                }
            }
            if(!isCycle) {
                // parse the branch taken
                const u2* temp = insns;
                temp += branchOffset;
                std::vector<int> tempInsOffsets = *insOffsets;
                std::map<u2, std::set<ObjectAccInfo*> > tempInterest = *interestRegObjMap;
                int newDepth = depth + 1;
                // If we reach the maximum branch depth, we exit the parse of the method to save the cost of parse
                if(newDepth >= MaxBranchDepth) {
                    for(unsigned int i = 0; i < methodAccInfo->args->size(); i++) {
                        flagObjAll(methodAccInfo->args->at(i));
                    }
                    *exitMethod = true;
                    return;
                }
                parseInsns(temp, methodAccInfo, chain, &tempInsOffsets, &tempInterest, newDepth, exitMethod);
            }
            
            // the continuation of the loop will parse the branch not taken
        } else if(opcode == OP_GOTO) {
            vdst = inst_aa(insns);
            width = (s1)vdst;
            // check if the goto will lead to an instruction cycle
            bool isCycle = false;
            int newOffset = currentOffset + width;
            for(unsigned int i = 0; i < insOffsets->size(); i++) {
                if(newOffset == insOffsets->at(i)) {
                    isCycle = true;
                    break;
                }
            }
            if(isCycle) {
                return;
            }
        } else if(opcode == OP_GOTO_16) {
            s4 offset = (s2) insns[1];
            width = offset;
            // check if the goto will lead to an instruction cycle
            bool isCycle = false;
            int newOffset = currentOffset + width;
            for(unsigned int i = 0; i < insOffsets->size(); i++) {
                if(newOffset == insOffsets->at(i)) {
                    isCycle = true;
                    break;
                }
            }
            if(isCycle) {
                return;
            }
        } else if(opcode == OP_GOTO_32) {
            s4 offset = insns[1];               // low-order 16 bits
            offset |= ((s4) insns[2]) << 16;    // high-order 16 bits
            width = offset;
            // check if the goto will lead to an instruction cycle
            bool isCycle = false;
            int newOffset = currentOffset + width;
            for(unsigned int i = 0; i < insOffsets->size(); i++) {
                if(newOffset == insOffsets->at(i)) {
                    isCycle = true;
                    break;
                }
            }
            if(isCycle) {
                return;
            }
        } else if(opcode == OP_PACKED_SWITCH || opcode == OP_SPARSE_SWITCH) {
            s4 offset;
            offset = insns[1] | (((s4) insns[2]) << 16);
            const u2* switchData = insns + offset;       // offset in 16-bit units
            u2 size;
            const s4* entries;

            /*
             * Packed switch data format:
             *  ushort ident = 0x0100 or ident = 0x0200  magic value
             *  ushort size             number of entries in the table
             *  int first_key or int keys[size]          first (and lowest) switch case value
             *  int targets[size]       branch targets, relative to switch opcode
             *
             * Total size is (4+size*2) or (2+size*4) 16-bit code units.
             */
            switchData++; // this is the space the magic value takes
            size = *switchData++;
            assert(size > 0);
            
            if(opcode == OP_PACKED_SWITCH) {
                switchData += 2; // this is the space the first key takes
            } else {
                switchData += 2 * size; // this is the space the keys take
            }

            /* The entries are guaranteed to be aligned on a 32-bit boundary;
             * we can treat them as a native int array.
             */
            entries = (const s4*) switchData;
            assert(((u4)entries & 0x3) == 0);
            for(int idx = 0; idx < size; idx++) {
                s4 offset = s4FromSwitchData(&entries[idx]);
                // check if the switch case will lead to an instruction cycle
                bool isCycle = false;
                int newOffset = currentOffset + offset;
                for(unsigned int i = 0; i < insOffsets->size(); i++) {
                    if(newOffset == insOffsets->at(i)) {
                        isCycle = true;
                        break;
                    }
                }
                if(!isCycle) {
                    // parse the branch taken
                    const u2* temp = insns;
                    temp += offset;
                    std::vector<int> tempInsOffsets = *insOffsets;
                    std::map<u2, std::set<ObjectAccInfo*> > tempInterest = *interestRegObjMap;
                    int newDepth = depth + 1;
                    // If we reach the maximum branch depth, we exit the parse of the method to save the cost of parse
                    if(newDepth >= MaxBranchDepth) {
                        for(unsigned int i = 0; i < methodAccInfo->args->size(); i++) {
                            flagObjAll(methodAccInfo->args->at(i));
                        }
                        *exitMethod = true;
                        return;
                    }
                    parseInsns(temp, methodAccInfo, chain, &tempInsOffsets, &tempInterest, newDepth, exitMethod);
                }
            }
        } else if(opcode == OP_INSTANCE_OF || opcode == OP_NEW_ARRAY || opcode == OP_CONST_4 || opcode == OP_NEG_INT || opcode == OP_NOT_INT
            || opcode == OP_NEG_LONG || opcode == OP_NOT_LONG || opcode == OP_NEG_FLOAT
            || opcode == OP_NEG_DOUBLE || opcode == OP_INT_TO_LONG || opcode == OP_INT_TO_FLOAT
            || opcode == OP_INT_TO_DOUBLE || opcode == OP_LONG_TO_INT || opcode == OP_LONG_TO_FLOAT
            || opcode == OP_LONG_TO_DOUBLE || opcode == OP_FLOAT_TO_INT || opcode == OP_FLOAT_TO_LONG
            || opcode == OP_FLOAT_TO_DOUBLE || opcode == OP_DOUBLE_TO_INT || opcode == OP_DOUBLE_TO_LONG
            || opcode == OP_DOUBLE_TO_FLOAT || opcode == OP_INT_TO_BYTE || opcode == OP_INT_TO_CHAR
            || opcode == OP_INT_TO_SHORT || opcode == OP_ADD_INT_2ADDR || opcode == OP_SUB_INT_2ADDR
            || opcode == OP_MUL_INT_2ADDR || opcode == OP_DIV_INT_2ADDR || opcode == OP_REM_INT_2ADDR
            || opcode == OP_AND_INT_2ADDR || opcode == OP_OR_INT_2ADDR || opcode == OP_XOR_INT_2ADDR
            || opcode == OP_SHL_INT_2ADDR || opcode == OP_SHR_INT_2ADDR || opcode == OP_USHR_INT_2ADDR
            || opcode == OP_ADD_LONG_2ADDR || opcode == OP_SUB_LONG_2ADDR || opcode == OP_MUL_LONG_2ADDR
            || opcode == OP_DIV_LONG_2ADDR || opcode == OP_REM_LONG_2ADDR || opcode == OP_AND_LONG_2ADDR
            || opcode == OP_OR_LONG_2ADDR || opcode == OP_XOR_LONG_2ADDR || opcode == OP_SHL_LONG_2ADDR
            || opcode == OP_SHR_LONG_2ADDR || opcode == OP_USHR_LONG_2ADDR || opcode == OP_ADD_FLOAT_2ADDR
            || opcode == OP_SUB_FLOAT_2ADDR || opcode == OP_MUL_FLOAT_2ADDR || opcode == OP_DIV_FLOAT_2ADDR
            || opcode == OP_REM_FLOAT_2ADDR || opcode == OP_ADD_DOUBLE_2ADDR|| opcode == OP_SUB_DOUBLE_2ADDR
            || opcode == OP_MUL_DOUBLE_2ADDR || opcode == OP_DIV_DOUBLE_2ADDR || opcode == OP_REM_DOUBLE_2ADDR
            || opcode == OP_ADD_INT_LIT16 || opcode == OP_RSUB_INT || opcode == OP_MUL_INT_LIT16
            || opcode == OP_DIV_INT_LIT16 || opcode == OP_REM_INT_LIT16 || opcode == OP_AND_INT_LIT16
            || opcode == OP_OR_INT_LIT16 || opcode == OP_XOR_INT_LIT16) {
            vdst = inst_a(insns);
            interestRegObjMap->erase(vdst);
        } else if(opcode == OP_CONST_16 || opcode == OP_CONST || opcode == OP_CONST_HIGH16
            || opcode == OP_CONST_WIDE_16 || opcode == OP_CONST_WIDE_32 || opcode == OP_CONST_WIDE
            || opcode == OP_CONST_WIDE_HIGH16 || opcode == OP_CONST_STRING || opcode == OP_CONST_STRING_JUMBO
            || opcode == OP_NEW_INSTANCE || opcode == OP_CMPL_FLOAT || opcode == OP_CMPG_FLOAT
            || opcode == OP_CMPL_DOUBLE || opcode == OP_CMPG_DOUBLE || opcode == OP_CMP_LONG
            || opcode == OP_ADD_INT || opcode == OP_SUB_INT || opcode == OP_MUL_INT
            || opcode == OP_DIV_INT || opcode == OP_REM_INT || opcode == OP_AND_INT
            || opcode == OP_OR_INT || opcode == OP_XOR_INT || opcode == OP_SHL_INT
            || opcode == OP_SHR_INT || opcode == OP_USHR_INT || opcode == OP_ADD_LONG
            || opcode == OP_SUB_LONG || opcode == OP_MUL_LONG || opcode == OP_DIV_LONG
            || opcode == OP_REM_LONG || opcode == OP_AND_LONG || opcode == OP_OR_LONG
            || opcode == OP_XOR_LONG || opcode == OP_SHL_LONG || opcode == OP_SHR_LONG
            || opcode == OP_USHR_LONG || opcode == OP_ADD_FLOAT || opcode == OP_SUB_FLOAT
            || opcode == OP_MUL_FLOAT || opcode == OP_DIV_FLOAT || opcode == OP_REM_FLOAT
            || opcode == OP_ADD_DOUBLE || opcode == OP_SUB_DOUBLE || opcode == OP_MUL_DOUBLE
            || opcode == OP_DIV_DOUBLE || opcode == OP_REM_DOUBLE || opcode == OP_ADD_INT_LIT8
            || opcode == OP_RSUB_INT_LIT8 || opcode == OP_MUL_INT_LIT8 || opcode == OP_DIV_INT_LIT8
            || opcode == OP_REM_INT_LIT8 || opcode == OP_AND_INT_LIT8 || opcode == OP_OR_INT_LIT8
            || opcode == OP_XOR_INT_LIT8 || opcode == OP_SHL_INT_LIT8 || opcode == OP_SHR_INT_LIT8
            || opcode == OP_USHR_INT_LIT8) {
            vdst = inst_aa(insns);
            interestRegObjMap->erase(vdst);
        } else if(opcode == OP_THROW) {
            return;
        } else if(opcode == OP_CONST_CLASS) {
            // TODO: check if need to to any operation
            vdst = inst_aa(insns);
            interestRegObjMap->erase(vdst);
        } else if(opcode == OP_MONITOR_ENTER || opcode == OP_MONITOR_EXIT) {// we set this field as always need to be migrated
            // do nothing
        } else if(opcode == OP_CHECK_CAST || opcode == OP_FILL_ARRAY_DATA) {
            // do nothing
        } else if(opcode == OP_ARRAY_LENGTH)  { // we would migrate the length of array anyway
            vdst = inst_a(insns);
            // erase to set the result not be interest any more
            interestRegObjMap->erase(vdst);
        } else if(opcode == OP_FILLED_NEW_ARRAY || opcode == OP_FILLED_NEW_ARRAY_RANGE) {
            u4 arg5;
            //ref = insns[1];             // class ref
            vdst = insns[2];            // first 4 regs -or- range base

            if (opcode == OP_FILLED_NEW_ARRAY_RANGE) {
                vsrc1 = inst_aa(insns);  // #of elements 
                arg5 = -1;              // silence compiler warning
            } else {
                arg5 = inst_a(insns);
                vsrc1 = inst_b(insns);   // #of elements
            }
            if (opcode == OP_FILLED_NEW_ARRAY_RANGE) {
                for (int i = 0; i < vsrc1; i++) {
                    if(interestRegObjMap->find(vdst + i) != interestRegObjMap->end()) {
                        flagVecAll(&((*interestRegObjMap)[vdst + i]));
                    }
                }
            } else {
                assert(vsrc1 <= 5);
                if (vsrc1 == 5) {
                    if(interestRegObjMap->find(arg5) != interestRegObjMap->end()) {
                        flagVecAll(&((*interestRegObjMap)[arg5]));
                    }
                    vsrc1--;
                }
                for (int i = 0; i < vsrc1; i++) {
                    if(interestRegObjMap->find(vdst & 0x0f) != interestRegObjMap->end()) {
                        flagVecAll(&((*interestRegObjMap)[vdst & 0x0f]));
                    }
                    vdst >>= 4;
                }
            }
        } else if(opcode == OP_AGET || opcode == OP_AGET_WIDE || opcode == OP_AGET_OBJECT
            || opcode == OP_AGET_BOOLEAN || opcode == OP_AGET_BYTE || opcode == OP_AGET_CHAR
            || opcode == OP_AGET_SHORT) {
            u2 arrayInfo = insns[1];
            //vdst = inst_aa(insns);
            vsrc1 = arrayInfo & 0xff;
            if(interestRegObjMap->find(vsrc1) != interestRegObjMap->end()) {
                flagVecAll(&((*interestRegObjMap)[vsrc1]));
            }
            interestRegObjMap->erase(vdst);
            ObjectAccInfo* objAccInfo = new ObjectAccInfo();
            objAccInfo->allFlag = true;
            objAccInfo->inArray = true;
            (*interestRegObjMap)[vdst].insert(objAccInfo);
        } else if(opcode == OP_APUT_OBJECT) {
            vdst = inst_aa(insns);
            flagVecAllArray(&((*interestRegObjMap)[vdst]));
        } else if(opcode == OP_IPUT || opcode == OP_IPUT_WIDE || opcode == OP_IPUT_BOOLEAN 
            || opcode == OP_IPUT_BYTE || opcode == OP_IPUT_CHAR || opcode == OP_IPUT_SHORT 
            || opcode == OP_IPUT_VOLATILE || opcode == OP_IPUT_WIDE_VOLATILE
            || opcode == OP_SPUT_VOLATILE || opcode == OP_SPUT_WIDE_VOLATILE
            || opcode == OP_SPUT || opcode == OP_SPUT_WIDE || opcode == OP_SPUT_BOOLEAN
            || opcode == OP_SPUT_BYTE || opcode == OP_SPUT_CHAR || opcode == OP_SPUT_SHORT
            || opcode == OP_APUT || opcode == OP_APUT_WIDE || opcode == OP_APUT_BOOLEAN
            || opcode == OP_APUT_BYTE || opcode == OP_APUT_CHAR || opcode == OP_APUT_SHORT) {
            // do nothing
        } else if(opcode == OP_UNUSED_3E || opcode == OP_UNUSED_3F || opcode == OP_UNUSED_40
            || opcode == OP_UNUSED_41 || opcode == OP_UNUSED_42 || opcode == OP_UNUSED_43
            || opcode == OP_UNUSED_73 || opcode == OP_UNUSED_79 || opcode == OP_UNUSED_7A
            || opcode == OP_UNUSED_FF) {
            ALOGE("encountering error instruction code, opcode is: %d", opcode);
        } else {
            ALOGE("methodParser unrecognizable opcode: %d", opcode);
        }
    }
}

MethodAccInfo* parseMethod(Method* method, std::set<Method*>* chain) {
    if(methodResMap.find(method) != methodResMap.end()) {
        return methodResMap[method];
    }
    MethodAccInfo* methodAccInfo = new MethodAccInfo();
    methodAccInfo->method = method;
    populateMethodAccInfo(methodAccInfo);
    bool isCycle = false;
    // check if this method makes an invocation cycle, if true, then set all the parameters as need to be migrate all
    if(chain->find(method) != chain->end()) {
        isCycle = true;
    }
    // a method invocation cycle, an abstract or native method cannot be parsed, then we just set all the parameters as need migration
    if(isCycle || dvmIsNativeMethod(method) || dvmIsAbstractMethod(method)) {
        for(unsigned int idx = 0; idx < methodAccInfo->args->size(); idx++) {
            flagObjAll(methodAccInfo->args->at(idx));
        }
        methodResMap[method] = methodAccInfo;
        return methodAccInfo;
    }
    chain->insert(method);
    // declare a map which will contain the list of registers the method should track
    // in each register, we use a vector to track all the possible object this vector might store
    std::map<u2, std::set<ObjectAccInfo*> > interestRegObjMap;
    // sets the count to be the number of arguments and initiate them, and initialize interest registers
    DexParameterIterator iterator;
    const char* descriptor;
    dexParameterIteratorInit(&iterator, &method->prototype);
    for(int i = 0; i < method->insSize; i++) {
        if(i == 0 && !dvmIsStaticMethod(method)) {
            interestRegObjMap[method->registersSize - method->insSize + i].insert(methodAccInfo->args->at(i));
        }
        if(i > 0 || dvmIsStaticMethod(method)) {
            descriptor = dexParameterIteratorNextDescriptor(&iterator);
            if(descriptor == NULL) {
                //ALOGE("methodParser find NULL descriptor, insSize: %d, i: %d, method: %s.%s", method->insSize, i, method->clazz->descriptor, method->name);
                break;
            }
            // we only cares object parameter
            if(*descriptor == 'L' || *descriptor == '[') {
                interestRegObjMap[method->registersSize - method->insSize + i].insert(methodAccInfo->args->at(i));
            }
        }
    }
    const u2* insns = method->insns;
    //u4 insnsSize = dvmGetMethodInsnsSize(method);
    std::vector<int> insOffsets;
    int depth = 0;
    bool exitMethod = false;
    parseInsns(insns, methodAccInfo, chain, &insOffsets, &interestRegObjMap, depth, &exitMethod);
    
    chain->erase(method);
    methodResMap[method] = methodAccInfo;
    
    return methodAccInfo;
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

void depthTraverse(ObjectAccInfo* objAccInfo, int depth) {
    if(objAccInfo->allFlag) {
    //    ALOGE("methodParser depth: %d, allFlag is: %d", depth, objAccInfo->allFlag);
        return;
    }
    for(unsigned int i = 0; i < objAccInfo->fieldSet.size(); i++) {
    //    ALOGE("methodParser depth: %d, offset: %d, value is: %d", depth, i, objAccInfo->fieldSet[i] != NULL);
        if(objAccInfo->fieldSet[i] != NULL) {
            depthTraverse(objAccInfo->fieldSet[i], depth + 1);
        }
    }
}

void writeObjAccInfo(ObjectAccInfo* objAccInfo, std::ofstream* dstfile) {
    std::queue<std::vector<ObjectAccInfo*>* > frontier;
    std::vector<ObjectAccInfo*> first;
    first.push_back(objAccInfo);
    frontier.push(&first);
    while(!frontier.empty()) {
        std::vector<ObjectAccInfo*>* accVector = frontier.front();
        frontier.pop();
        for(unsigned int j = 0; j < accVector->size(); j++) {
            if(accVector->at(j) == NULL) {
                // would not access this field
                *dstfile << "0";
            } else if(accVector->at(j) != NULL && !(accVector->at(j)->allFlag)) {
                // will access this field
                frontier.push(&(accVector->at(j)->fieldSet));
                *dstfile << "1";
            } else {
                // will access this field but requires to migrate all
                *dstfile << "2";
            }
        }
        *dstfile << "|";
    }
    *dstfile << std::endl;
}

/*static ObjectAccInfo* getTopAccInfo(ObjectAccInfo* objAccInfo) {
    ObjectAccInfo* tmp = objAccInfo;
    while(tmp != NULL) {
        if(tmp->belonging == NULL) {
            return tmp;
        } else {
            tmp = tmp->belonging;
        }
    }
    return NULL;
}

static void writeOnAirObject(MethodAccInfo* methodAccInfo) {

}

void writeObjTrackInfo(ObjectAccInfo* objAccInfo, short currentArg, MethodAccInfo* methodAccInfo, std::ofstream* dstfile) {
    std::queue<std::vector<ObjectAccInfo*>* > frontier;
    std::vector<ObjectAccInfo*> first;
    first.push_back(objAccInfo);
    frontier.push(&first);
    while(!frontier.empty()) {
        std::vector<ObjectAccInfo*>* accVector = frontier.front();
        frontier.pop();
        for(unsigned int i = 0; i < accVector->size(); i++) {
            if(accVector->at(i) != NULL) {
                frontier.push(&(accVector->at(i)->fieldSet));
                for(unsigned int j = 0; j < accVector->at(i)->trackSet.size(); j++) {
                    bool isFirst = true;
                    for(std::set<ObjectAccInfo*>::iterator it = accVector->at(i)->trackSet[j]->begin(); it != accVector->at(i)->trackSet[j]->end(); ++it) {
                        ObjectAccInfo* trackAcc = *it;
                        if(!isFirst) {
                            *dstfile << " * ";
                        }
                        isFirst = false;
                        // case 1: track is just the field itself
                        if(trackAcc == accVector->at(i)->fieldSet[j]) {
                            *dstfile << "S" << " " << trackAcc.idx;
                        } else {
                            ObjectAccInfo* topAccInfo = getTopAccInfo(trackAcc);
                            bool isProcessed = false;
                            for(unsigned int k = 0; k < methodAccInfo->args->size(); k++) {
                                // this track comes from a field of argument
                                if(topAccInfo == methodAccInfo->args->at(k)) {
                                    // case 2: track is from the argument itself
                                    if(k == currentArg) {
                                        *dstfile << "G" << " " << trackAcc.idx;
                                    }
                                    // case 3: track is from another argument
                                    else {
                                        *dstfile << "O" << " " << k << " " << trackAcc.idx;
                                    }
                                    isProcessed = true;
                                }
                            }
                            if(isProcessed) {
                                continue;
                            }
                            for(unsigned int k = 0; k < methodAccInfo->globalClazz->size(); k++) {
                                // case 4: this track comes from a static class
                                if(topAccInfo == methodAccInfo->globalClazz->at(k)) {
                                    *dstfile << "C" << " " << methodAccInfo->globalClazz->at(k)->clazz->descriptor << " " << trackAcc.idx;
                                    isProcessed = true;
                                }
                            }
                            if(isProcessed) {
                                continue;
                            }
                            // case 5: this track comes from air
                        }
                    }
                }
                *dstfile << "^";
            }
        }
        *dstfile << "|";
    }
    *dstfile << std::endl;
}*/

/* set the index no for each objectAccInfo */
static void indexObjects(MethodAccInfo* methodAccInfo, std::vector<ObjectAccInfo*>* objList) {
    std::queue<ObjectAccInfo*> frontier;
    for(unsigned int i = 0; i < methodAccInfo->globalClazz->size(); i++) {
        frontier.push(methodAccInfo->globalClazz->at(i));
    }
    for(unsigned int i = 0; i < methodAccInfo->args->size(); i++) {
        frontier.push(methodAccInfo->args->at(i));
    }
    int index = 1;
    while(!frontier.empty()) {
        ObjectAccInfo* objAccInfo = frontier.front();
        frontier.pop();
        if(objAccInfo->idx < 0) {
            continue;
        }
        objAccInfo->idx = index++;
        objList->push_back(objAccInfo);
        for(unsigned int i = 0; i < objAccInfo->fieldSet.size(); i++) {
            if(objAccInfo->filedSet[i] != NULL) {
                frontier.push(objAccInfo->filedSet[i]);
            }
            if(objAccInfo->trackSet[i] != NULL) {
                for(std::set<ObjectAccInfo*>::iterator it = objAccInfo->trackSet[i]->begin(); it != objAccInfo->trackSet[i]->end(); ++it) {
                    frontier.push_back(*it);
                }
            }
        }
    }
}

/* save ObjectAccInfo with structure */
static void saveStructureToFile(MethodAccInfo* methodAccInfo, std::vector<ObjectAccInfo*>* objList, std::ofstream* dstfile) {
    *dstfile << methodAccInfo->globalClazz->size() << " " << methodAccInfo->args->size() << endl;
    for(unsigned int i = 0; i < objList->size(); i++) {
        ObjectAccInfo* objAccInfo = objList->at(i);
        *dstfile << objAccInfo->idx << " " << objAccInfo->allFlag << " ";
        for(unsigned int j = 0; j < objAccInfo->filedSet.size(); j++) {
            if(j != 0) {
                *dstfile << '|';
            }
            if(objAccInfo->fieldSet[j] == NULL) {
                *dstfile << -1;
            } else {
                *dstfile << objAccInfo->fieldSet[j]->idx;
            }
        }
        for(unsigned int j = 0; j < objAccInfo->trackSet.size(); j++) {
            if(j != 0) {
                *dstfile << '|';
            }
            if(objAccInfo->trackSet[j] == NULL) {
                *dstfile << -1;
            } else {
                int first = true;
                for(std::set<ObjectAccInfo*>::iterator it = objAccInfo->trackSet[j]->begin(); it != objAccInfo->trackSet[j]->end(); ++it) {
                    if(!first) {
                        *dstfile << ',';
                    }
                    *dstfile << *it->idx;
                    first = false;
                }
            }
        }
        *dstfile << " ";
        if(i < methodAccInfo->globalClazz->size()) {
            *dstfile << methodAccInfo->globalClazz->at(i)->clazz->descriptor;
        }
        *dstfile << std::endl;
    }
}

void persistMethodInfo(MethodAccInfo* methodAccInfo, const char* fileName) {
    std::ofstream dstfile;
    dstfile.open(fileName, std::ios::app);
    Method* method = methodAccInfo->method;
    // output method identification
    dstfile << method->clazz->descriptor << " " << method->name << " " << method->idx << std::endl;
    for(unsigned int i = 0; i < methodAccInfo->args->size(); i++) {
        writeObjAccInfo(methodAccInfo->args->at(i), &dstfile);
    }
    dstfile << std::endl;
    /*for(unsigned int i = 0; i < methodAccInfo->globalClazz->size(); i++) {
        dstfile << methodAccInfo->globalClazz->at(i)->clazz->descriptor << std::endl;
        writeObjAccInfo(methodAccInfo->globalClazz->at(i), &dstfile);
    }
    dstfile << std::endl;*/
    dstfile.close();
}

void depthTraverseResult(ObjectAccResult* objAccResult, int depth) {
    if(objAccResult->allFlag) {
        //ALOGE("methodParser result depth: %d, allFlag is: %d", depth, objAccResult->allFlag);
        return;
    }
    //ALOGE("methodParser result depth: %d, value is: %u:%u", depth, objAccResult->migrate, objAccResult->highbits == NULL ? 0 : *(objAccResult->highbits));
    for(unsigned int i = 0; i < objAccResult->fieldSet.size(); i++) {
        //ALOGE("methodParser result depth: %d, offset: %d, value is: %d", depth, i, objAccResult->fieldSet[i] != NULL);
        if(objAccResult->fieldSet[i] != NULL) {
            depthTraverseResult(objAccResult->fieldSet[i], depth + 1);
        }
    }
}

void setMigrateBits(ObjectAccResult* objAccResult) {
    if(objAccResult->allFlag) {
        return;
    }
    objAccResult->migrate = 0x00000000U;
    unsigned int lowBitSize = objAccResult->fieldSet.size() > 32 ? 32 : objAccResult->fieldSet.size();
    for(unsigned int i = 0; i < lowBitSize; i++) {
        if(objAccResult->fieldSet[i] != NULL) {
            objAccResult->migrate = objAccResult->migrate | (1U << i);
        }
    }
    if(objAccResult->fieldSet.size() > 32) {
        u4 sz = (objAccResult->fieldSet.size() - 1) >> 5;
        objAccResult->highbits = (u4*)calloc(sz, 4);
        for(unsigned int i = 32; i < objAccResult->fieldSet.size(); i++) {
            if(objAccResult->fieldSet[i] != NULL) {
                int32_t val = 1U << (i & 0x1F);
                int32_t* ptr = (int32_t*)objAccResult->highbits + ((i - 32) >> 5);
                *ptr = *ptr | val;
            }
        }
    }
    for(unsigned int i = 0; i < objAccResult->fieldSet.size(); i++) {
        if(objAccResult->fieldSet[i] != NULL) {
            setMigrateBits(objAccResult->fieldSet[i]);
        }
    }
}

void retrieveMethodInfo(std::map<char*, MethodAccResult*, charscomp>* methodAccMap, const char* fileName) {
    std::ifstream srcfile;
    srcfile.open(fileName);
    std::string line;
    while(std::getline(srcfile, line)) {
        MethodAccResult* methodAccResult = new MethodAccResult();
        char* methodInfo = new char[line.length() + 1];
        strcpy(methodInfo, line.c_str());
        (*methodAccMap)[methodInfo] = methodAccResult;
        methodAccResult->args = new std::vector<ObjectAccResult*>();
        while(true) {
            std::getline(srcfile, line);
            if(line.compare("") == 0) {
                break;
            }
            const char* argInfo = line.c_str();
            ObjectAccResult* objAccResult = new ObjectAccResult();
            methodAccResult->args->push_back(objAccResult);
            if(argInfo[0] == '2') {
                objAccResult->allFlag = true;
                continue;
            }
            std::queue<ObjectAccResult*> frontier;
            frontier.push(objAccResult);
            ObjectAccResult* current = objAccResult;
            for(unsigned int i = 2; i < strlen(argInfo) && !frontier.empty(); i++) {
                if(argInfo[i] == '|') {
                    frontier.pop();
                    if(!frontier.empty()) {
                        current = frontier.front();
                    }
                } else if(argInfo[i] == '0') {
                    current->fieldSet.push_back(NULL);
                } else if(argInfo[i] == '1') {
                    ObjectAccResult* newAcc = new ObjectAccResult();
                    current->fieldSet.push_back(newAcc);
                    frontier.push(newAcc);
                } else {
                    ObjectAccResult* newAcc = new ObjectAccResult();
                    newAcc->allFlag = true;
                    current->fieldSet.push_back(newAcc);
                }
            }
        }
        /*methodAccResult->globalClazz = new std::vector<ClazzAccResult*>();
        while(true) {
            std::getline(srcfile, line);
            if(line.compare("") == 0) {
                break;
            }
            ClazzAccResult* clzAccResult = new ClazzAccResult();
            methodAccResult->globalClazz->push_back(clzAccResult);
            clzAccResult->clazz = strdup(line.c_str());
            std::getline(srcfile, line);
            const char* clzInfo = line.c_str();
            if(clzInfo[0] == '2') {
                clzAccResult->allFlag = true;
                continue;
            }
            std::queue<ObjectAccResult*> frontier;
            frontier.push(clzAccResult);
            ObjectAccResult* current = clzAccResult;
            for(unsigned int i = 2; i < strlen(clzInfo) && !frontier.empty(); i++) {
                if(clzInfo[i] == '|') {
                    frontier.pop();
                    if(!frontier.empty()) {
                        current = frontier.front();
                    }
                } else if(clzInfo[i] == '0') {
                    current->fieldSet.push_back(NULL);
                } else if(clzInfo[i] == '1') {
                    ObjectAccResult* newAcc = new ObjectAccResult();
                    current->fieldSet.push_back(newAcc);
                    frontier.push(newAcc);
                } else {
                    ObjectAccResult* newAcc = new ObjectAccResult();
                    newAcc->allFlag = true;
                    current->fieldSet.push_back(newAcc);
                }
            }
        }*/
        // set migrate bits for this method info
        for(unsigned int i = 0; i < methodAccResult->args->size(); i++) {
            setMigrateBits(methodAccResult->args->at(i));
        }
        /*for(unsigned int i = 0; i < methodAccResult->globalClazz->size(); i++) {
            setMigrateBits(methodAccResult->globalClazz->at(i));
        }*/
    }
    srcfile.close();
}
