
#include "Dalvik.h"
#include "ParserCommon.h"
#include "CustomizedClass.h"
#include "libdex/DexCatch.h"
#include <sys/time.h>

struct ParsedMethoOffInfo;

unsigned int MaxSubCount = 15;
extern char* basePath;

extern std::vector<DvmDex*> loadedDex;
extern ClassObject* javaLangObject;
extern std::set<ClassObject*>* exemptClzs;
extern std::set<ClassObject*>* exemptIfs;
std::fstream poffFile;
std::fstream presultFile;
std::fstream presultFileTxt;
extern std::map<const char*, int, charscomp>* strOffMap;
extern std::map<int, const char*>* offStrMap;
std::map<Method*, ParsedMethoOffInfo*>* parsedMethodOffMap = new std::map<Method*, ParsedMethoOffInfo*>();
//std::map<Method*, MethodAccInfo*> virtualResMap;
//std::map<Method*, MethodAccInfo*> interResMap;

// method declaration
static void copyParseInfo(ParseInfo* src, ParseInfo* dst);
static void freeParseInfo(ParseInfo* parseInfo);
static bool checkInterest(ParseInfo* parseInfo);
void loadStructureInFile(MethodAccInfo* methodAccInfo, int offStart, int length);
void parseInsns(const u2* insns, MethodAccInfo* methodAccInfo, std::vector<Method*>* chain, int depth, bool* exitMethod);

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

void populateMethodAccInfo(MethodAccInfo* methodAccInfo) {
    Method* method = methodAccInfo->method;
    methodAccInfo->args = new std::vector<ObjectAccInfo*>();
    for(int i = 0; i < method->insSize; i++) {
        methodAccInfo->args->push_back(new ObjectAccInfo());
    }
    methodAccInfo->globalClazz = new std::vector<ClazzAccInfo*>();
}

/* check if the objects in the vector are all flaged as migrating all */
static bool isVecFlagedAll(std::set<ObjectAccInfo*>* objsVector) {
    if(objsVector == NULL) {
        return true;
    }
    std::vector<ObjectAccInfo*>* toProcess = new std::vector<ObjectAccInfo*>();
    std::set<ObjectAccInfo*>* processVec = new std::set<ObjectAccInfo*>();
    for(std::set<ObjectAccInfo*>::iterator it = objsVector->begin(); it != objsVector->end(); ++it) {
        toProcess->push_back(*it);
        processVec->insert(*it);
    }
    for(unsigned int i = 0; i < toProcess->size(); i++) {
        ObjectAccInfo* objAccInfo = (*toProcess)[i];
        ObjectAccInfo* tmp = objAccInfo;
        bool isflaged = false;
        do {
            if(tmp->allFlag) {
                isflaged = true;
                break;
            }
            tmp = tmp->belonging;
        } while(tmp != NULL);
        if(!isflaged) {
            return false;
        }
        for(unsigned int j = 0; j < objAccInfo->trackSet.size(); j++) {
            if(objAccInfo->trackSet[j] == NULL) {
                continue;
            }
            for(std::set<ObjectAccInfo*>::iterator it = objAccInfo->trackSet[j]->begin(); it != objAccInfo->trackSet[j]->end(); ++it) {
                if(processVec->find(*it) == processVec->end()) {
                    toProcess->push_back(*it);
                    processVec->insert(*it);
                }
            }
        }
    }
    delete toProcess;
    delete processVec;
    return true;
}

static void flagObjAll(ObjectAccInfo* objAccInfoArg) {
    std::vector<ObjectAccInfo*> toProcess;
    std::set<ObjectAccInfo*> processVec;
    toProcess.push_back(objAccInfoArg);
    processVec.insert(objAccInfoArg);
    for(unsigned int i = 0; i < toProcess.size(); i++) {
        ObjectAccInfo* objAccInfo = toProcess[i];
        objAccInfo->allFlag = true;
        for(unsigned int j = 0; j < objAccInfo->fieldSet.size(); j++) {
            if(objAccInfo->trackSet[j] == NULL) {
                continue;
            }
            for(std::set<ObjectAccInfo*>::iterator it = objAccInfo->trackSet[j]->begin(); it != objAccInfo->trackSet[j]->end(); ++it) {
                if(processVec.find(*it) == processVec.end()) {
                    toProcess.push_back(*it);
                    processVec.insert(*it);
                }
            }
        }
    }
}

/* flag all the objects in vector as migrating all */
static void flagVecAll(std::set<ObjectAccInfo*>* objsVector) {
    std::vector<ObjectAccInfo*> toProcess;
    std::set<ObjectAccInfo*> processVec;
    for(std::set<ObjectAccInfo*>::iterator it = objsVector->begin(); it != objsVector->end(); ++it) {
        toProcess.push_back(*it);
        processVec.insert(*it);
    }
    for(unsigned int i = 0; i < toProcess.size(); i++) {
        ObjectAccInfo* objAccInfo = toProcess[i];
        objAccInfo->allFlag = true;
        for(unsigned int j = 0; j < objAccInfo->fieldSet.size(); j++) {
            if(objAccInfo->trackSet[j] == NULL) {
                continue;
            }
            for(std::set<ObjectAccInfo*>::iterator it = objAccInfo->trackSet[j]->begin(); it != objAccInfo->trackSet[j]->end(); ++it) {
                if(processVec.find(*it) == processVec.end()) {
                    toProcess.push_back(*it);
                    processVec.insert(*it);
                }
            }
        }
    }
}

/* flag all the objects in vector as migrating all */
static void flagVecAllArray(std::set<ObjectAccInfo*>* objsVector) {
    std::vector<ObjectAccInfo*> toProcess;
    std::set<ObjectAccInfo*> processVec;
    for(std::set<ObjectAccInfo*>::iterator it = objsVector->begin(); it != objsVector->end(); ++it) {
        toProcess.push_back(*it);
        processVec.insert(*it);
    }
    for(unsigned int i = 0; i < toProcess.size(); i++) {
        ObjectAccInfo* objAccInfo = toProcess[i];
        objAccInfo->allFlag = true;
        objAccInfo->inArray = true;
        for(unsigned int j = 0; j < objAccInfo->fieldSet.size(); j++) {
            if(objAccInfo->trackSet[j] == NULL) {
                continue;
            }
            for(std::set<ObjectAccInfo*>::iterator it = objAccInfo->trackSet[j]->begin(); it != objAccInfo->trackSet[j]->end(); ++it) {
                if(processVec.find(*it) == processVec.end()) {
                    toProcess.push_back(*it);
                    processVec.insert(*it);
                }
            }
        }
    }
}

static void unionObjectFieldInfo(ObjectAccInfo* dstObjAccInfo, ObjectAccInfo* srcObjAccInfo, std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap, bool isDstBranch) {
    (*addrMap)[srcObjAccInfo] = dstObjAccInfo;
    if(srcObjAccInfo->allFlag) {
        dstObjAccInfo->allFlag = true;
    }
    if(srcObjAccInfo->inArray) {
        dstObjAccInfo->inArray = true;
    }
    if(dstObjAccInfo->fieldSet.size() < srcObjAccInfo->fieldSet.size()) {
        dstObjAccInfo->nullBranchFlags.resize(srcObjAccInfo->fieldSet.size());
        dstObjAccInfo->fieldSet.resize(srcObjAccInfo->fieldSet.size());
        dstObjAccInfo->trackSet.resize(srcObjAccInfo->trackSet.size());
    }
    for(unsigned int i = 0; i < srcObjAccInfo->fieldSet.size(); i++) {
        if(!(dstObjAccInfo->nullBranchFlags[i])) {
            dstObjAccInfo->nullBranchFlags[i] = srcObjAccInfo->nullBranchFlags[i] || dstObjAccInfo->nullBranchFlags[i];
            if(srcObjAccInfo->fieldSet[i] == NULL && srcObjAccInfo->trackSet[i] == NULL) {
                dstObjAccInfo->nullBranchFlags[i] = true;
            }
            if(isDstBranch && dstObjAccInfo->fieldSet[i] == NULL && dstObjAccInfo->trackSet[i] == NULL) {
                dstObjAccInfo->nullBranchFlags[i] = true;
            }
        }
        if(srcObjAccInfo->fieldSet[i] == NULL) {
            continue;
        }
        if(dstObjAccInfo->fieldSet[i] == NULL) {
            dstObjAccInfo->fieldSet[i] = new ObjectAccInfo();
            dstObjAccInfo->fieldSet[i]->belonging = dstObjAccInfo;
        }
        unionObjectFieldInfo(dstObjAccInfo->fieldSet[i], srcObjAccInfo->fieldSet[i], addrMap, isDstBranch);
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
    newAccInfo->nullBranchFlags.resize(srcTrackObj->nullBranchFlags.size());
    newAccInfo->fieldSet.resize(srcTrackObj->fieldSet.size());
    newAccInfo->trackSet.resize(srcTrackObj->trackSet.size());
    for(unsigned int i = 0; i < newAccInfo->trackSet.size(); i++) {
        if(srcTrackObj->trackSet[i] == NULL) {
            continue;
        }
        newAccInfo->trackSet[i] = new std::set<ObjectAccInfo*>();
        for(std::set<ObjectAccInfo*>::iterator it = srcTrackObj->trackSet[i]->begin(); it != srcTrackObj->trackSet[i]->end(); ++it) {
            if((*addrMap).find(*it) == (*addrMap).end()) {
                createMatchTrack(*it, addrMap);
            }
            newAccInfo->trackSet[i]->insert((*addrMap)[*it]);
        }
    }
}

static void handleUnmatchTrack(std::set<ObjectAccInfo*>* dstTrackSet, ObjectAccInfo* srcTrackObj, std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap, std::set<ObjectAccInfo*>* fieldAccSet) {
    bool isHandled = false;
    for(std::set<ObjectAccInfo*>::iterator it = dstTrackSet->begin(); it != dstTrackSet->end(); ++it) {
        if(fieldAccSet->find(*it) == fieldAccSet->end()) {
            isHandled = true;
            (*addrMap)[srcTrackObj] = *it;
            (*it)->allFlag = (*it)->allFlag || srcTrackObj->allFlag;
            (*it)->inArray = (*it)->inArray || srcTrackObj->inArray;
            if((*it)->trackSet.size() < srcTrackObj->trackSet.size()) {
                (*it)->nullBranchFlags.resize(srcTrackObj->nullBranchFlags.size());
                (*it)->fieldSet.resize(srcTrackObj->fieldSet.size());
                (*it)->trackSet.resize(srcTrackObj->trackSet.size());
            }
            for(unsigned int i = 0; i < srcTrackObj->trackSet.size(); i++) {
                if(srcTrackObj->trackSet[i] == NULL || srcTrackObj->trackSet[i]->empty()) {
                    continue;
                }
                if((*it)->trackSet[i] == NULL) {
                    (*it)->trackSet[i] = new std::set<ObjectAccInfo*>();
                }
                for(std::set<ObjectAccInfo*>::iterator tit = srcTrackObj->trackSet[i]->begin(); tit != srcTrackObj->trackSet[i]->end(); ++tit) {
                    if((*addrMap).find(*tit) == (*addrMap).end()) {
                        handleUnmatchTrack((*it)->trackSet[i], *tit, addrMap, fieldAccSet);
                    }
                    (*it)->trackSet[i]->insert((*addrMap)[*tit]);
                }
            }
            break;
        }
    }
    if(!isHandled) {
        createMatchTrack(srcTrackObj, addrMap);
    }
}

static void unionTracks(std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap, std::set<ObjectAccInfo*>* fieldAccSet) {
    // addr should have all the mapping between dst and src already
    std::set<ObjectAccInfo*> srcSet;
    for(std::map<ObjectAccInfo*, ObjectAccInfo*>::iterator it = addrMap->begin(); it != addrMap->end(); ++it) {
        srcSet.insert(it->first);
    }
    for(std::set<ObjectAccInfo*>::iterator it = srcSet.begin(); it != srcSet.end(); ++it) {
        ObjectAccInfo* srcObjAccInfo = *it;
        for(unsigned int i = 0; i < srcObjAccInfo->trackSet.size(); i++) {
            if(srcObjAccInfo->trackSet[i] == NULL || srcObjAccInfo->trackSet[i]->size() == 0) {
                continue;
            }
            ObjectAccInfo* dstObjAccInfo = (*addrMap)[srcObjAccInfo];
            if(dstObjAccInfo->trackSet[i] == NULL) {
                dstObjAccInfo->trackSet[i] = new std::set<ObjectAccInfo*>();
            }
            for(std::set<ObjectAccInfo*>::iterator trkit = srcObjAccInfo->trackSet[i]->begin(); trkit != srcObjAccInfo->trackSet[i]->end(); ++trkit) {
                if((*addrMap).find(*trkit) == (*addrMap).end()) {
                    // first check if there is an objectAccInfo in dst track which is not from an field set
                    handleUnmatchTrack(dstObjAccInfo->trackSet[i], *trkit, addrMap, fieldAccSet);
                }
                dstObjAccInfo->trackSet[i]->insert((*addrMap)[*trkit]);
            }
        }
    }
}
/*
static void unionObjectTrackInfo(ObjectAccInfo* dstObjAccInfo, ObjectAccInfo* srcObjAccInfo, std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap, std::set<ObjectAccInfo*>* fieldAccSet) {
    for(unsigned int i = 0; i < srcObjAccInfo->trackSet.size(); i++) {
        if(dstObjAccInfo->fieldSet[i] != NULL && srcObjAccInfo->fieldSet[i] != NULL) {
            unionObjectTrackInfo(dstObjAccInfo->fieldSet[i], srcObjAccInfo->fieldSet[i], addrMap, fieldAccSet);
        }
        if(srcObjAccInfo->trackSet[i] == NULL || srcObjAccInfo->trackSet[i]->size() == 0) {
            continue;
        }
        if(dstObjAccInfo->trackSet[i] == NULL) {
            dstObjAccInfo->trackSet[i] = new std::set<ObjectAccInfo*>();
        }
        for(std::set<ObjectAccInfo*>::iterator it = srcObjAccInfo->trackSet[i]->begin(); it != srcObjAccInfo->trackSet[i]->end(); ++it) {
            if((*addrMap).find(*it) == (*addrMap).end()) {
                // first check if there is an objectAccInfo in dst track which is not from an field set
                handleUnmatchTrack(dstObjAccInfo->trackSet[i], *it, addrMap, fieldAccSet);
            }
            dstObjAccInfo->trackSet[i]->insert((*addrMap)[*it]);
        }
        //if(dstObjAccInfo->trackSet[i]->size() > 100) {
        //    ALOGE("union track get a large size: %u, the src size is: %u", dstObjAccInfo->trackSet[i]->size(), srcObjAccInfo->trackSet[i]->size());
        //}
    }
}*/

static void unionClazzFieldInfo(MethodAccInfo* dstAccInfo, MethodAccInfo* srcAccInfo, std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap, bool isDstBranch) {
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
        unionObjectFieldInfo(dstAccInfo->globalClazz->at(j), srcAccInfo->globalClazz->at(i), addrMap, isDstBranch);
    }
}
/*
static void unionClazzTrackInfo(MethodAccInfo* dstAccInfo, MethodAccInfo* srcAccInfo, std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap, std::set<ObjectAccInfo*>* fieldAccSet) {
    for(unsigned int i = 0; i < srcAccInfo->globalClazz->size(); i++) {
        unsigned int j;
        for(j = 0; j < dstAccInfo->globalClazz->size(); j++) {
            if(srcAccInfo->globalClazz->at(i)->clazz == dstAccInfo->globalClazz->at(j)->clazz) {
                break;
            }
        }
        unionObjectTrackInfo(dstAccInfo->globalClazz->at(j), srcAccInfo->globalClazz->at(i), addrMap, fieldAccSet);
    }
}*/

static void unionReturnObjs(MethodAccInfo* dstAccInfo, MethodAccInfo* srcAccInfo, std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap) {
    if(srcAccInfo->returnObjs == NULL || srcAccInfo->returnObjs->size() == 0) {
        return;
    }
    if(dstAccInfo->returnObjs == NULL) {
        dstAccInfo->returnObjs = new std::set<ObjectAccInfo*>();
    }
    for(std::set<ObjectAccInfo*>::iterator it = srcAccInfo->returnObjs->begin(); it != srcAccInfo->returnObjs->end(); ++it) {
        if((*addrMap).find(*it) == (*addrMap).end()) {
            createMatchTrack(*it, addrMap);
        }
        dstAccInfo->returnObjs->insert((*addrMap)[*it]);
    }
}

static void getFieldAccSet(MethodAccInfo* methodAccInfo, std::set<ObjectAccInfo*>* fieldAccSet) {
    std::vector<ObjectAccInfo*> processList;
    for(unsigned int i = 0; i < methodAccInfo->args->size(); i++) {
        processList.push_back(methodAccInfo->args->at(i));
    }
    for(unsigned int i = 0; i < methodAccInfo->globalClazz->size(); i++) {
        processList.push_back(methodAccInfo->globalClazz->at(i));
    }
    for(unsigned int i = 0; i < processList.size(); i++) {
        fieldAccSet->insert(processList[i]);
        for(unsigned int j = 0; j < processList[i]->fieldSet.size(); j++) {
            if(processList[i]->fieldSet[j] != NULL) {
                processList.push_back(processList[i]->fieldSet[j]);
            }
        }
    }
}

static void unionMethodAccInfo(MethodAccInfo* dstAccInfo, MethodAccInfo* srcAccInfo, std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap, bool isDstBranch) {
    // union the field access info for each args
    for(unsigned int i = 0; i < srcAccInfo->args->size(); i++) {
        unionObjectFieldInfo(dstAccInfo->args->at(i), srcAccInfo->args->at(i), addrMap, isDstBranch);
    }
    // union the class field access info for each class
    unionClazzFieldInfo(dstAccInfo, srcAccInfo, addrMap, isDstBranch);
    // find out all the object which is in the fieldSet of args and clazz recursively
    std::set<ObjectAccInfo*> fieldAccSet;
    getFieldAccSet(dstAccInfo, &fieldAccSet);
    // union the field track info for each args
    unionTracks(addrMap, &fieldAccSet);
    /*for(unsigned int i = 0; i < srcAccInfo->args->size(); i++) {
        unionObjectTrackInfo(dstAccInfo->args->at(i), srcAccInfo->args->at(i), addrMap, &fieldAccSet);
    }*/
    // union the class field track info for each class
    //unionClazzTrackInfo(dstAccInfo, srcAccInfo, addrMap, &fieldAccSet);
    // union the return objects
    unionReturnObjs(dstAccInfo, srcAccInfo, addrMap);
}

/* Union the two method access info into the dstAccInfo */
static void unionMethodAccInfo(MethodAccInfo* dstAccInfo, MethodAccInfo* srcAccInfo, bool isDstBranch) {
    //ALOGE("union method info: %p - %s.%s, sub method is: %p - %s.%s", dstAccInfo->method, dstAccInfo->method->clazz->descriptor, dstAccInfo->method->name, srcAccInfo->method, srcAccInfo->method->clazz->descriptor, srcAccInfo->method->name);
    std::map<ObjectAccInfo*, ObjectAccInfo*> addrMap;
    unionMethodAccInfo(dstAccInfo, srcAccInfo, &addrMap, isDstBranch);
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
            (*it)->nullBranchFlags.resize(srcAccInfo->fieldSet.size());
            (*it)->fieldSet.resize(srcAccInfo->fieldSet.size());
            (*it)->trackSet.resize(srcAccInfo->trackSet.size());
        }
    }
    for(unsigned int i = 0; i < srcAccInfo->fieldSet.size(); i++) {
        if(srcAccInfo->fieldSet[i] == NULL) {
            if(srcAccInfo->nullBranchFlags[i]) {
                for(std::set<ObjectAccInfo*>::iterator it = dstAccInfoList->begin(); it != dstAccInfoList->end(); ++it) {
                    (*it)->nullBranchFlags[i] = true;
                }
            }
            continue;
        }
        std::set<ObjectAccInfo*> fieldList;
        for(std::set<ObjectAccInfo*>::iterator it = dstAccInfoList->begin(); it != dstAccInfoList->end(); ++it) {
            if((unsigned int)(srcAccInfo->fieldSet[i]) == 0x46b415e8) {
                ALOGE("find the specified address parsing, dst addr: %p", *it);
            }
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

void mergeObjectAccTrackInfo(std::set<ObjectAccInfo*>* dstAccInfoList, ObjectAccInfo* srcAccInfo, std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap, std::set<ObjectAccInfo*>* changeCache, std::set<ObjectAccInfo*>* fieldAccSet);

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
    newAccInfo->nullBranchFlags.resize(srcTrackObj->fieldSet.size());
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

static std::set<ObjectAccInfo*>* handleUnmatchVecTrack(std::set<ObjectAccInfo*>* dstTrackSet, ObjectAccInfo* srcTrackObj, std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap, std::set<ObjectAccInfo*>* fieldAccSet) {
    bool isHandled = false;
    if(dstTrackSet != NULL) {
        for(std::set<ObjectAccInfo*>::iterator it = dstTrackSet->begin(); it != dstTrackSet->end(); ++it) {
            if(fieldAccSet->find(*it) == fieldAccSet->end()) {
                isHandled = true;
                std::set<ObjectAccInfo*>* tempMapping = new std::set<ObjectAccInfo*>();
                tempMapping->insert(*it);
                (*addrMap)[srcTrackObj] = *tempMapping;
                (*it)->allFlag = (*it)->allFlag || srcTrackObj->allFlag;
                (*it)->inArray = (*it)->inArray || srcTrackObj->inArray;
                if((*it)->trackSet.size() < srcTrackObj->trackSet.size()) {
                    (*it)->nullBranchFlags.resize(srcTrackObj->nullBranchFlags.size());
                    (*it)->fieldSet.resize(srcTrackObj->fieldSet.size());
                    (*it)->trackSet.resize(srcTrackObj->trackSet.size());
                    (*it)->mergeSet.resize(srcTrackObj->trackSet.size());
                }
                for(unsigned int i = 0; i < srcTrackObj->trackSet.size(); i++) {
                    if(srcTrackObj->trackSet[i] == NULL || srcTrackObj->trackSet[i]->empty()) {
                        continue;
                    }
                    if((*it)->trackSet[i] == NULL) {
                        (*it)->trackSet[i] = new std::set<ObjectAccInfo*>();
                    }
                    for(std::set<ObjectAccInfo*>::iterator tit = srcTrackObj->trackSet[i]->begin(); tit != srcTrackObj->trackSet[i]->end(); ++tit) {
                        if((*addrMap).find(*tit) == (*addrMap).end()) {
                            std::set<ObjectAccInfo*>* currentTrack;
                            currentTrack = handleUnmatchVecTrack((*it)->trackSet[i], *tit, addrMap, fieldAccSet);
                            if(currentTrack == NULL) { // indicates that it comes from the method of createVecMatchTrack
                                (*it)->trackSet[i]->insert((*addrMap)[*tit].begin(), (*addrMap)[*tit].end());
                            } else {
                                (*it)->trackSet[i]->insert(currentTrack->begin(), currentTrack->end());
                                delete currentTrack;
                            }
                        } else {
                            (*it)->trackSet[i]->insert((*addrMap)[*tit].begin(), (*addrMap)[*tit].end());
                        }
                    }
                }
                addrMap->erase(srcTrackObj);
                return tempMapping;
            }
        }
    }
    if(!isHandled) {
        createVecMatchTrack(srcTrackObj, addrMap);
    }
    return NULL;
}

static void mergeTracks(std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap, std::set<ObjectAccInfo*>* changeCache, std::set<ObjectAccInfo*>* fieldAccSet) {
    // addr should have all the mapping between dst and src already
    std::set<ObjectAccInfo*> srcSet;
    for(std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >::iterator it = addrMap->begin(); it != addrMap->end(); ++it) {
        srcSet.insert(it->first);
    }
    for(std::set<ObjectAccInfo*>::iterator it = srcSet.begin(); it != srcSet.end(); ++it) {
        ObjectAccInfo* srcAccInfo = *it;
        for(unsigned int i = 0; i < srcAccInfo->trackSet.size(); i++) {
            if(srcAccInfo->trackSet[i] == NULL || srcAccInfo->trackSet[i]->size() == 0) {
                continue;
            }
            changeCache->insert((*addrMap)[srcAccInfo].begin(), (*addrMap)[srcAccInfo].end());
            for(std::set<ObjectAccInfo*>::iterator dstit = (*addrMap)[srcAccInfo].begin(); dstit != (*addrMap)[srcAccInfo].end(); ++dstit) {
                ObjectAccInfo* dstAccInfo = *dstit;
                dstAccInfo->mergeSet.resize(dstAccInfo->trackSet.size());
                // indicates that the one in the track should not change, there is no assign to the track
                if(srcAccInfo->trackSet[i]->size() == 1 && srcAccInfo->trackSet[i]->find(srcAccInfo->fieldSet[i]) != srcAccInfo->trackSet[i]->end()) {
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
                    // if the subAccInfo has a null branch, we should retain the previous track set of the object
                    if(srcAccInfo->nullBranchFlags[i] && dstAccInfo->trackSet[i] != NULL) {
                        dstAccInfo->mergeSet[i]->insert(dstAccInfo->trackSet[i]->begin(), dstAccInfo->trackSet[i]->end());
                    }
                }
                for(std::set<ObjectAccInfo*>::iterator trkit = srcAccInfo->trackSet[i]->begin(); trkit != srcAccInfo->trackSet[i]->end(); ++trkit) {
                    if((*addrMap).find(*trkit) == (*addrMap).end()) {
                        std::set<ObjectAccInfo*>* currentTrack;
                        currentTrack = handleUnmatchVecTrack(dstAccInfo->trackSet[i], *trkit, addrMap, fieldAccSet);
                        if(currentTrack == NULL) { // indicates that it comes from the method of createVecMatchTrack
                            dstAccInfo->mergeSet[i]->insert((*addrMap)[*trkit].begin(), (*addrMap)[*trkit].end());
                        } else {
                            dstAccInfo->mergeSet[i]->insert(currentTrack->begin(), currentTrack->end());
                            delete currentTrack;
                        }
                    } else {
                        dstAccInfo->mergeSet[i]->insert((*addrMap)[*trkit].begin(), (*addrMap)[*trkit].end());
                    }
                }
            }
        }
    }
}
/*
static void mergeObjectTrack(ObjectAccInfo* dstAccInfo, ObjectAccInfo* srcAccInfo, std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap, std::set<ObjectAccInfo*>* changeCache, std::set<ObjectAccInfo*>* fieldAccSet) {
    //pushSingle(changeCache, dstAccInfo);
    changeCache->insert(dstAccInfo);
    dstAccInfo->mergeSet.resize(dstAccInfo->trackSet.size());
    for(unsigned int i = 0; i < srcAccInfo->trackSet.size(); i++) {
        if(srcAccInfo->fieldSet[i] != NULL) {
            if((unsigned int)(srcAccInfo->fieldSet[i]) == 0x46b415e8) {
                ALOGE("in track specified address parsing, dst addr: %p", dstAccInfo);
            }
            mergeObjectAccTrackInfo(dstAccInfo->trackSet[i], srcAccInfo->fieldSet[i], addrMap, changeCache, fieldAccSet);
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
            // if the subAccInfo has a null branch, we should retain the previous track set of the object
            if(srcAccInfo->nullBranchFlags[i] && dstAccInfo->trackSet[i] != NULL) {
                dstAccInfo->mergeSet[i]->insert(dstAccInfo->trackSet[i]->begin(), dstAccInfo->trackSet[i]->end());
            }
        }
        for(std::set<ObjectAccInfo*>::iterator it = srcAccInfo->trackSet[i]->begin(); it != srcAccInfo->trackSet[i]->end(); ++it) {
            if((*addrMap).find(*it) == (*addrMap).end()) {
                std::set<ObjectAccInfo*>* currentTrack;
                currentTrack = handleUnmatchVecTrack(dstAccInfo->trackSet[i], *it, addrMap, fieldAccSet);
                if(currentTrack == NULL) { // indicates that it comes from the method of createVecMatchTrack
                    dstAccInfo->mergeSet[i]->insert((*addrMap)[*it].begin(), (*addrMap)[*it].end());
                } else {
                    dstAccInfo->mergeSet[i]->insert(currentTrack->begin(), currentTrack->end());
                    delete currentTrack;
                }
            } else {
                dstAccInfo->mergeSet[i]->insert((*addrMap)[*it].begin(), (*addrMap)[*it].end());
            }
        }
    }
}

void mergeObjectAccTrackInfo(std::set<ObjectAccInfo*>* dstAccInfoList, ObjectAccInfo* srcAccInfo, std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap, std::set<ObjectAccInfo*>* changeCache, std::set<ObjectAccInfo*>* fieldAccSet) {
    for(std::set<ObjectAccInfo*>::iterator it = dstAccInfoList->begin(); it != dstAccInfoList->end(); ++it) {
        mergeObjectTrack(*it, srcAccInfo, addrMap, changeCache, fieldAccSet);
    }
}*/

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

/*static void mergeGlobalClazzTrack(MethodAccInfo* methodAccInfo, MethodAccInfo* subAccInfo, std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap, std::set<ObjectAccInfo*>* changeCache, std::set<ObjectAccInfo*>* fieldAccSet) {
    for(unsigned int i = 0; i < subAccInfo->globalClazz->size(); i++) {
        unsigned int j;
        for(j = 0; j < methodAccInfo->globalClazz->size(); j++) {
            if(subAccInfo->globalClazz->at(i)->clazz == methodAccInfo->globalClazz->at(j)->clazz) {
                break;
            }
        }
        mergeObjectTrack(methodAccInfo->globalClazz->at(j), subAccInfo->globalClazz->at(i), addrMap, changeCache, fieldAccSet);
    }
}*/

static void mergeMethodReturnInfo(MethodAccInfo* methodAccInfo, MethodAccInfo* subAccInfo, std::map<ObjectAccInfo*, std::set<ObjectAccInfo*> >* addrMap) {
    if(subAccInfo->returnObjs == NULL || subAccInfo->returnObjs->size() == 0) {
        return;
    }
    methodAccInfo->curMethodReturns = new std::set<ObjectAccInfo*>();
    for(std::set<ObjectAccInfo*>::iterator it = subAccInfo->returnObjs->begin(); it != subAccInfo->returnObjs->end(); ++it) {
        if((*addrMap).find(*it) == (*addrMap).end()) {
            createVecMatchTrack(*it, addrMap);
        }
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

static void applyMergeToTrack(std::set<ObjectAccInfo*>* changeCache) {
    for (std::set<ObjectAccInfo*>::iterator it = changeCache->begin(); it != changeCache->end(); ++it) {
        ObjectAccInfo* objAccInfo = *it;
        if(objAccInfo->mergeSet.size() == 0) {
            // indicates we have processed this obj in previous iteration
            continue;
        }
        if(objAccInfo->mergeSet.size() != objAccInfo->trackSet.size()) {
            ALOGE("the size of merge is: %u, track is: %u", objAccInfo->mergeSet.size(), objAccInfo->trackSet.size());
        }
        assert(objAccInfo->mergeSet.size() == objAccInfo->trackSet.size());
        for(unsigned int j = 0; j < objAccInfo->trackSet.size(); j++) {
            if(objAccInfo->mergeSet[j] == NULL) {
                continue;
            }
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
    //ALOGE("the subacinfo with method: %s %s %d", subAccInfo->method->clazz->descriptor, subAccInfo->method->name, subAccInfo->method->idx);
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
    std::set<ObjectAccInfo*> fieldAccSet;
    getFieldAccSet(methodAccInfo, &fieldAccSet);
    std::set<ObjectAccInfo*>* changeCache = new std::set<ObjectAccInfo*>();
    /*switch (count) {
    case 5:
        reg = vsrc1 & 0x0f;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccTrackInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(4), &addrMap, changeCache, &fieldAccSet);
        }
    case 4:
        reg = vdst >> 12;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccTrackInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(3), &addrMap, changeCache, &fieldAccSet);
        }
    case 3:
        reg = (vdst & 0x0f00) >> 8;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccTrackInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(2), &addrMap, changeCache, &fieldAccSet);
        }
    case 2:
        reg = (vdst & 0x00f0) >> 4;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccTrackInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(1), &addrMap, changeCache, &fieldAccSet);
        }
    case 1:
        reg = vdst & 0x0f;
        if(interestRegObjMap->find(reg) != interestRegObjMap->end()) {
            mergeObjectAccTrackInfo(&((*interestRegObjMap)[reg]), subAccInfo->args->at(0), &addrMap, changeCache, &fieldAccSet);
        }
    default:
        ;
    }
    // merge global track info
    mergeGlobalClazzTrack(methodAccInfo, subAccInfo, &addrMap, changeCache, &fieldAccSet);*/
    mergeTracks(&addrMap, changeCache, &fieldAccSet);
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
    std::set<ObjectAccInfo*> fieldAccSet;
    getFieldAccSet(methodAccInfo, &fieldAccSet);
    std::set<ObjectAccInfo*>* changeCache = new std::set<ObjectAccInfo*>();
    /*for(int i = 0; i < vsrc1; i++) {
        if(interestRegObjMap->find(vdst + i) != interestRegObjMap->end()) {
            mergeObjectAccTrackInfo(&((*interestRegObjMap)[vdst + i]), subAccInfo->args->at(i), &addrMap, changeCache, &fieldAccSet);
        }
    }
    // merge global track info
    mergeGlobalClazzTrack(methodAccInfo, subAccInfo, &addrMap, changeCache, &fieldAccSet);*/
    mergeTracks(&addrMap, changeCache, &fieldAccSet);
    applyMergeToTrack(changeCache);
    delete changeCache;
    mergeMethodReturnInfo(methodAccInfo, subAccInfo, &addrMap);
}

/*void handleLoop(const u2* insns, MethodAccInfo* methodAccInfo, std::vector<int>* insOffsets, int startIdx, std::map<u2, std::vector<ObjectAccInfo*> >* interestRegObjMap) {
    
}*/

int catchBranches = 0;
static void handleCatchBranch(Method* method, ParseInfo* toParse, std::set<ParseInfo*>* executions) {
    int relPc = toParse->insoff;
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
            if(toParse->insOffsets->find(catchOffset) != toParse->insOffsets->end()) {
                isCycle = true;
            }
            if(!isCycle) {
                // parse the branch taken
                ParseInfo* catchParseInfo = new ParseInfo();
                copyParseInfo(toParse, catchParseInfo);
                catchParseInfo->insoff = catchOffset;
                executions->insert(catchParseInfo);
                catchBranches++;
            }
        }
    }
}

static void replaceNewWithDest(ObjectAccInfo* newObjAccInfo, std::map<ObjectAccInfo*, ObjectAccInfo*>* addrMap) {
    std::queue<ObjectAccInfo*> frontier;
    frontier.push(newObjAccInfo);
    std::set<ObjectAccInfo*> addedToQue;
    addedToQue.insert(newObjAccInfo);
    while(!frontier.empty()) {
        ObjectAccInfo* objAccInfo = frontier.front();
        frontier.pop();
        for(unsigned int i = 0; i < objAccInfo->fieldSet.size(); i++) {
            if(objAccInfo->fieldSet[i] != NULL) {
                if((*addrMap)[objAccInfo->fieldSet[i]] != NULL) {
                    objAccInfo->fieldSet[i] = (*addrMap)[objAccInfo->fieldSet[i]];
                } else if(addedToQue.find(objAccInfo->fieldSet[i]) == addedToQue.end()) {
                    frontier.push(objAccInfo->fieldSet[i]);
                    addedToQue.insert(objAccInfo);
                }
            }
            if(objAccInfo->trackSet[i] != NULL) {
                std::set<ObjectAccInfo*> changeset;
                for(std::set<ObjectAccInfo*>::iterator it = objAccInfo->trackSet[i]->begin(); it != objAccInfo->trackSet[i]->end(); ++it) {
                    if((*addrMap)[*it] != NULL) {
                        changeset.insert(*it);
                    } else if(addedToQue.find(*it) == addedToQue.end()) {
                        frontier.push(*it);
                        addedToQue.insert(*it);
                    }
                }
                for(std::set<ObjectAccInfo*>::iterator it = changeset.begin(); it != changeset.end(); ++it) {
                    objAccInfo->trackSet[i]->erase(*it);
                    objAccInfo->trackSet[i]->insert((*addrMap)[*it]);
                }
            }
        }
    }
}

int mergecount = 0;
static ParseInfo* findLeastOffParse(std::set<ParseInfo*>* executions) {
    // union execution parse info with the same instruction offset
    std::map<int, ParseInfo*> offParseMap;
    bool ischanged = false;
    for(std::set<ParseInfo*>::iterator it = executions->begin(); it != executions->end(); ++it) {
        if(offParseMap.find((*it)->insoff) == offParseMap.end()) {
            offParseMap[(*it)->insoff] = *it;
        } else {
            mergecount++;
            ischanged = true;
            ParseInfo* dst = offParseMap[(*it)->insoff];
            dst->affectTry = true;
            ParseInfo* src = *it;
            std::map<ObjectAccInfo*, ObjectAccInfo*> addrMap;
            unionMethodAccInfo(dst->methodAccInfo, src->methodAccInfo, &addrMap, true);
            for(std::map<u2, std::set<ObjectAccInfo*> >::iterator mapit = src->interestRegObjMap->begin(); mapit != src->interestRegObjMap->end(); ++mapit) {
                for(std::set<ObjectAccInfo*>::iterator setit = mapit->second.begin(); setit != mapit->second.end(); ++setit) {
                    if(addrMap[*setit] == NULL) {
                        replaceNewWithDest(*setit, &addrMap);
                        (*(dst->interestRegObjMap))[mapit->first].insert(*setit);
                    } else {
                        (*(dst->interestRegObjMap))[mapit->first].insert(addrMap[*setit]);
                    }
                }
            }
            dst->insOffsets->insert(src->insOffsets->begin(), src->insOffsets->end());
            freeParseInfo(src);
        }
    }
    if(ischanged) {
        executions->clear();
        for(std::map<int, ParseInfo*>::iterator it = offParseMap.begin(); it != offParseMap.end(); ++it) {
            executions->insert(it->second);
        }
    }

    int minOff = INT_MAX;
    ParseInfo* result = NULL;
    for(std::set<ParseInfo*>::iterator it = executions->begin(); it != executions->end(); ++it) {
        if((*it)->insoff < minOff) {
            minOff = (*it)->insoff;
            result = *it;
        }
    }
    return result;
}

static void endParse(MethodAccInfo* methodAccInfo, ParseInfo* toParse, std::set<ParseInfo*>* executions) {
    unionMethodAccInfo(methodAccInfo, toParse->methodAccInfo, false);
    executions->erase(toParse);
    freeParseInfo(toParse);
}

void pchain(std::vector<Method*>* chain) {
    for(unsigned int i = 0; i < chain->size(); i++) {
        ALOGE("%s.%s", chain->at(i)->clazz->descriptor, chain->at(i)->name);
    }
}

void parseInsns(const u2* methInsns, MethodAccInfo* methodAccInfo, std::vector<Method*>* chain, int depth, bool* exitMethod) {
    if(*exitMethod) {
        return;
    }
    int branches = 0;
    Method* method = methodAccInfo->method;
    DvmDex* methodClassDex = method->clazz->pDvmDex;
    u2 vsrc1, vdst;
    u4 ref;
    Opcode opcode = (Opcode) 0;
    int width, currentOffset;
    std::set<ParseInfo*> executions;
    ParseInfo* parseInfo = new ParseInfo();
    parseInfo->insoff = 0;
    parseInfo->insOffsets = new std::set<int>();
    MethodAccInfo* methdAcc = new MethodAccInfo();
    methdAcc->method = method;
    populateMethodAccInfo(methdAcc);
    parseInfo->methodAccInfo = methdAcc;
    parseInfo->interestRegObjMap = new std::map<u2, std::set<ObjectAccInfo*> >();
    // sets the count to be the number of arguments and initiate them, and initialize interest registers
    DexParameterIterator iterator;
    const char* descriptor;
    dexParameterIteratorInit(&iterator, &method->prototype);
    for(int i = 0; i < method->insSize; i++) {
        if(i == 0 && !dvmIsStaticMethod(method)) {
            (*(parseInfo->interestRegObjMap))[method->registersSize - method->insSize + i].insert(parseInfo->methodAccInfo->args->at(i));
        }
        if(i > 0 || dvmIsStaticMethod(method)) {
            descriptor = dexParameterIteratorNextDescriptor(&iterator);
            if(descriptor == NULL) {
                //ALOGE("methodParser find NULL descriptor, insSize: %d, i: %d, method: %s.%s", method->insSize, i, method->clazz->descriptor, method->name);
                break;
            }
            // we only cares object parameter
            if(*descriptor == 'L' || *descriptor == '[') {
                (*(parseInfo->interestRegObjMap))[method->registersSize - method->insSize + i].insert(parseInfo->methodAccInfo->args->at(i));
            }
        }
    }
    executions.insert(parseInfo);
    while(!executions.empty()) {
        ParseInfo* toParse = findLeastOffParse(&executions);
        const u2* insns = methInsns + toParse->insoff;
        width = dexGetWidthFromInstruction(insns);
        toParse->insOffsets->insert(toParse->insoff);
        currentOffset = toParse->insoff;
        opcode = dexOpcodeFromCodeUnit(*insns);
        std::map<u2, std::set<ObjectAccInfo*> >* interestRegObjMap = toParse->interestRegObjMap;
        if(toParse->affectTry) {
            // each instruction might raise an exception, go to the corresponding handler to process
            handleCatchBranch(method, toParse, &executions);
        }
        toParse->affectTry = false;
        if(opcode == OP_IGET || opcode == OP_IGET_WIDE || opcode == OP_IGET_OBJECT || opcode == OP_IGET_BOOLEAN 
            || opcode == OP_IGET_BYTE || opcode == OP_IGET_CHAR || opcode == OP_IGET_SHORT 
            || opcode == OP_IGET_VOLATILE || opcode == OP_IGET_OBJECT_VOLATILE || opcode == OP_IGET_WIDE_VOLATILE) {
            vdst = inst_a(insns);
            vsrc1 = inst_b(insns);
            // check if the source register is in our interest list
            if(interestRegObjMap->find(vsrc1) == interestRegObjMap->end()) {
                // erase to initiate
                interestRegObjMap->erase(vdst);
                goto finally;
            }
            ref = insns[1];
            unsigned int offset;
            InstField* ifield = (InstField*) dvmDexGetResolvedField(methodClassDex, ref); 
            if (ifield == NULL) {
                ifield = resolveInstField(method->clazz, ref);
                if(ifield == NULL) { // we should have encountered a wrong version field branch
                    endParse(methodAccInfo, toParse, &executions);
                    continue;
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
                    objAccInfo->nullBranchFlags.resize(offset + 1);
                    objAccInfo->fieldSet.resize(offset + 1);
                    objAccInfo->trackSet.resize(offset + 1);
                }
                // if the field has not been setup, then set the field
                if(objAccInfo->trackSet[offset] == NULL || (objAccInfo->nullBranchFlags[offset] && objAccInfo->fieldSet[offset] == NULL)) {
                    ObjectAccInfo* fieldInfo = new ObjectAccInfo();
                    //ALOGE("ifield name is: %s, %s, address: %p", ifield->clazz->descriptor, ifield->name, fieldInfo);
                    fieldInfo->belonging = objAccInfo;
                    if(objAccInfo->inArray) {
                        fieldInfo->inArray = true;
                    }
                    objAccInfo->fieldSet[offset] = fieldInfo;
                    if(objAccInfo->trackSet[offset] == NULL) {
                        objAccInfo->trackSet[offset] = new std::set<ObjectAccInfo*>();
                    }
                    objAccInfo->trackSet[offset]->insert(objAccInfo->fieldSet[offset]);
                }
                if(executions.size() == 1) {
                    objAccInfo->nullBranchFlags[offset] = false;
                }
                if(opcode == OP_IGET_OBJECT || opcode == OP_IGET_OBJECT_VOLATILE) {
                    ((*interestRegObjMap)[vdst]).insert(objAccInfo->trackSet[offset]->begin(), objAccInfo->trackSet[offset]->end());
                }
            }
            if(opcode == OP_IGET_OBJECT || opcode == OP_IGET_OBJECT_VOLATILE) {
                toParse->affectTry = true;
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
                    endParse(methodAccInfo, toParse, &executions);
                    continue;
                }
            }
            offset = (ifield->byteOffset - sizeof(Object)) >> 2;
            
            // both src object and dst are not in our interest
            if(interestRegObjMap->find(vdst) == interestRegObjMap->end() && interestRegObjMap->find(vsrc1) == interestRegObjMap->end()) {
                goto finally;
            } else if(interestRegObjMap->find(vdst) == interestRegObjMap->end() && interestRegObjMap->find(vsrc1) != interestRegObjMap->end()) { 
                // only src object are in interest, in this case, we set the offset to be an arbitrary one to make sure it will not pollute the original data
                std::set<ObjectAccInfo*> srcVector = (*interestRegObjMap)[vsrc1];
                for(std::set<ObjectAccInfo*>::iterator it = srcVector.begin(); it != srcVector.end(); ++it) {
                    ObjectAccInfo* interestAccInfo = *it;
                    if(interestAccInfo->trackSet.size() < offset + 1) {
                        interestAccInfo->nullBranchFlags.resize(offset + 1);
                        interestAccInfo->fieldSet.resize(offset + 1);
                        interestAccInfo->trackSet.resize(offset + 1);
                    }
                    if(interestAccInfo->trackSet[offset] != NULL) {
                        delete interestAccInfo->trackSet[offset];
                    }
                    interestAccInfo->trackSet[offset] = new std::set<ObjectAccInfo*>();
                    if(executions.size() == 1) {
                        interestAccInfo->nullBranchFlags[offset] = false;
                    }
                }
                goto finally;
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
                    interestAccInfo->nullBranchFlags.resize(offset + 1);
                    interestAccInfo->fieldSet.resize(offset + 1);
                    interestAccInfo->trackSet.resize(offset + 1);
                }
                if(interestAccInfo->trackSet[offset] != NULL) {
                    delete interestAccInfo->trackSet[offset];
                }
                interestAccInfo->trackSet[offset] = new std::set<ObjectAccInfo*>();
                interestAccInfo->trackSet[offset]->insert((*interestRegObjMap)[vdst].begin(), (*interestRegObjMap)[vdst].end());
                if(executions.size() == 1) {
                    interestAccInfo->nullBranchFlags[offset] = false;
                }
            }
            toParse->affectTry = true;
        } else if(opcode == OP_SGET_VOLATILE || opcode == OP_SGET_WIDE_VOLATILE || opcode == OP_SGET_OBJECT_VOLATILE
            || opcode == OP_SGET || opcode == OP_SGET_WIDE || opcode == OP_SGET_OBJECT || opcode == OP_SGET_BOOLEAN
            || opcode == OP_SGET_BYTE || opcode == OP_SGET_CHAR || opcode == OP_SGET_SHORT) {
            vdst = inst_a(insns);
            ref = insns[1];
            StaticField* sfield = (StaticField*)dvmDexGetResolvedField(methodClassDex, ref);
            if (sfield == NULL) {
                sfield = resolveStaticField(method->clazz, ref);
                if(sfield == NULL) { // we should have encountered a wrong version field branch
                    endParse(methodAccInfo, toParse, &executions);
                    continue;
                }
            }
            unsigned int offset = sfield - sfield->clazz->sfields;
            unsigned int i;
            for(i = 0; i < toParse->methodAccInfo->globalClazz->size(); i++) {
                if(sfield->clazz == toParse->methodAccInfo->globalClazz->at(i)->clazz) {
                    break;
                }
            }
            if(i == toParse->methodAccInfo->globalClazz->size()) { // The first time to deal this global class object
                ClazzAccInfo* clazzAccInfo = new ClazzAccInfo();
                clazzAccInfo->clazz = sfield->clazz;
                toParse->methodAccInfo->globalClazz->push_back(clazzAccInfo);
            }
            ClazzAccInfo* clazzAccInfo = toParse->methodAccInfo->globalClazz->at(i);
            if(clazzAccInfo->trackSet.size() < offset + 1) { // the current size of trackSet vector are not big enough
                clazzAccInfo->nullBranchFlags.resize(offset + 1);
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
            if(executions.size() == 1) {
                clazzAccInfo->nullBranchFlags[offset] = false;
            }
            interestRegObjMap->erase(vdst);
            // if the object is already set as migrate all, then ignore it
            //if(isVecFlagedAll(clazzAccInfo->trackSet[offset])) {
            //    continue;
            //}
            // add the destination register into the interest map
            if(opcode == OP_SGET_OBJECT_VOLATILE || opcode == OP_SGET_OBJECT) {
                (*interestRegObjMap)[vdst] = *(clazzAccInfo->trackSet[offset]);
                toParse->affectTry = true;
            }
        } else if(opcode == OP_SPUT_OBJECT || opcode == OP_SPUT_OBJECT_VOLATILE) {// if the dst is in the interest, the src class'es field should also be in interest
            vdst = inst_aa(insns);
            ref = insns[1];  
            StaticField* sfield = (StaticField*)dvmDexGetResolvedField(methodClassDex, ref);
            if (sfield == NULL) {
                sfield = resolveStaticField(method->clazz, ref);
                if(sfield == NULL) { // we should have encountered a wrong version field branch
                    endParse(methodAccInfo, toParse, &executions);
                    continue;
                }
            }
            unsigned int offset = sfield - sfield->clazz->sfields;
            unsigned int i;
            for(i = 0; i < toParse->methodAccInfo->globalClazz->size(); i++) {
                if(sfield->clazz == toParse->methodAccInfo->globalClazz->at(i)->clazz) {
                    break;
                }
            }
            if(i == toParse->methodAccInfo->globalClazz->size()) { // The first time to deal this global class object
                ClazzAccInfo* clazzAccInfo = new ClazzAccInfo();
                clazzAccInfo->clazz = sfield->clazz;
                toParse->methodAccInfo->globalClazz->push_back(clazzAccInfo);
            }
            ClazzAccInfo* clazzAccInfo = toParse->methodAccInfo->globalClazz->at(i);
            if(clazzAccInfo->trackSet.size() < offset + 1) { // the current size of trackSet vector are not big enough
                clazzAccInfo->nullBranchFlags.resize(offset + 1);
                clazzAccInfo->fieldSet.resize(offset + 1);
                clazzAccInfo->trackSet.resize(offset + 1);
            }
            // only src clazz are in interest, in this case, we set the offset to be an arbitrary one to make sure it will not pollute the original data
            if(interestRegObjMap->find(vdst) == interestRegObjMap->end()) {
                if(clazzAccInfo->trackSet[offset] != NULL) {
                    delete clazzAccInfo->trackSet[offset];
                }
                clazzAccInfo->trackSet[offset] = new std::set<ObjectAccInfo*>();
                goto finally;
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
            toParse->affectTry = true;
            if(executions.size() == 1) {
                clazzAccInfo->nullBranchFlags[offset] = false;
            }
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
                if(opcode == OP_MOVE_OBJECT || opcode == OP_MOVE_OBJECT_FROM16 || opcode == OP_MOVE_OBJECT_16) {
                    toParse->affectTry = true;
                }
            }
        } else if(opcode == OP_INVOKE_VIRTUAL || opcode == OP_INVOKE_VIRTUAL_RANGE) {
            vsrc1 = inst_aa(insns);      // AA (count) or BA (count + arg 5) 
            ref = insns[1];             // method ref 
            vdst = insns[2];            // 4 regs -or- first reg
            if(toParse->methodAccInfo->curMethodReturns != NULL) {
                delete toParse->methodAccInfo->curMethodReturns;
                toParse->methodAccInfo->curMethodReturns = NULL;
            }
            
            int voffset;
            Method* baseMethod;
            baseMethod = dvmDexGetResolvedMethod(methodClassDex, ref);
            if (baseMethod == NULL) {
                baseMethod = resolveMethod(method->clazz, ref, METHOD_VIRTUAL);
                if(baseMethod == NULL) { // we should have encountered a wrong version method branch
                    endParse(methodAccInfo, toParse, &executions);
                    continue;
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
                goto finally;
            }
            
            bool isLangObjectClass = baseMethod->clazz == javaLangObject;
            bool isExempt = (exemptClzs->find(baseMethod->clazz) != exemptClzs->end());
            if(isLangObjectClass || isExempt) {
                if(opcode == OP_INVOKE_VIRTUAL) {
                    methodRegsFlagAll(vsrc1, vdst, interestRegObjMap);
                } else {
                    rangeMethodRegsFlagAll(vsrc1, vdst, interestRegObjMap);
                }
                goto finally;
            }
            //ALOGE("methodParser parse virtual %s.%s, by %s.%s", baseMethod->clazz->descriptor, baseMethod->name, method->clazz->descriptor, method->name);
            MethodAccInfo* subAccInfo;
            //if(virtualResMap.find(baseMethod) != virtualResMap.end()) {
            //    subAccInfo = virtualResMap[baseMethod];
            //} else {
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
                    goto finally;
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
                    MethodAccInfo* toCallAccInfo = new MethodAccInfo();
                    toCallAccInfo->method = methodToCall;
                    // setup subcall method access info and parse
                    parseMethod(toCallAccInfo, chain);
                    unionMethodAccInfo(subAccInfo, toCallAccInfo, false);
                    freeMethodAccInfo(toCallAccInfo);
                }
            //    virtualResMap[baseMethod] = subAccInfo;
            //}
            if(opcode == OP_INVOKE_VIRTUAL) {
                mergeMethodArgs(vsrc1, vdst, interestRegObjMap, toParse->methodAccInfo, subAccInfo);
            } else {
                mergeRangeMethodArgs(vsrc1, vdst, interestRegObjMap, toParse->methodAccInfo, subAccInfo);
            }
            freeMethodAccInfo(subAccInfo);
            toParse->affectTry = true;
        } else if(opcode == OP_INVOKE_INTERFACE || opcode == OP_INVOKE_INTERFACE_RANGE) { // see Interp.cpp-dvmInterpFindInterfaceMethod
            vsrc1 = inst_aa(insns);      // AA (count) or BA (count + arg 5) 
            ref = insns[1];             // method ref 
            vdst = insns[2];            // 4 regs -or- first reg
            if(toParse->methodAccInfo->curMethodReturns != NULL) {
                delete toParse->methodAccInfo->curMethodReturns;
                toParse->methodAccInfo->curMethodReturns = NULL;
            }
            
            Method* absMethod;
            absMethod = dvmDexGetResolvedMethod(methodClassDex, ref);
            if (absMethod == NULL) {
                absMethod = resolveInterfaceMethod(method->clazz, ref);
                 if(absMethod == NULL) { // we should have encountered a wrong version method branch
                     endParse(methodAccInfo, toParse, &executions);
                     continue;
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
                goto finally;
            }
            
            bool isExempt = (exemptIfs->find(absMethod->clazz) != exemptIfs->end());
            if(isExempt) {
                if(opcode == OP_INVOKE_INTERFACE) {
                    methodRegsFlagAll(vsrc1, vdst, interestRegObjMap);
                } else {
                    rangeMethodRegsFlagAll(vsrc1, vdst, interestRegObjMap);
                }
                goto finally;
            }
            
            //ALOGE("methodParser parse interface %s.%s, by %s.%s", absMethod->clazz->descriptor, absMethod->name, method->clazz->descriptor, method->name);
            MethodAccInfo* subAccInfo;
            //if(interResMap.find(absMethod) != interResMap.end()) {
            //    subAccInfo = interResMap[absMethod];
            //} else {
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
                    goto finally;
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
                    MethodAccInfo* toCallAccInfo = new MethodAccInfo();
                    toCallAccInfo->method = methodToCall;
                    // setup subcall method access info and parse
                    parseMethod(toCallAccInfo, chain);
                    unionMethodAccInfo(subAccInfo, toCallAccInfo, false);
                    freeMethodAccInfo(toCallAccInfo);
                }
                //interResMap[absMethod] = subAccInfo;
            //}
            if(opcode == OP_INVOKE_INTERFACE) {
                mergeMethodArgs(vsrc1, vdst, interestRegObjMap, toParse->methodAccInfo, subAccInfo);
            } else {
                mergeRangeMethodArgs(vsrc1, vdst, interestRegObjMap, toParse->methodAccInfo, subAccInfo);
            }
            freeMethodAccInfo(subAccInfo);
            toParse->affectTry = true;
        } else if(opcode == OP_INVOKE_SUPER || opcode == OP_INVOKE_DIRECT || opcode == OP_INVOKE_STATIC 
            || opcode == OP_INVOKE_SUPER_RANGE || opcode == OP_INVOKE_DIRECT_RANGE || opcode == OP_INVOKE_STATIC_RANGE) {
            vsrc1 = inst_aa(insns);      // AA (count) or BA (count + arg 5) 
            ref = insns[1];             // method ref 
            vdst = insns[2];            // 4 regs -or- first reg
            if(toParse->methodAccInfo->curMethodReturns != NULL) {
                delete toParse->methodAccInfo->curMethodReturns;
                toParse->methodAccInfo->curMethodReturns = NULL;
            }
            
            // check if the method invocation involves interesting registers
            bool hasInterest;
            if(opcode == OP_INVOKE_SUPER || opcode == OP_INVOKE_DIRECT || opcode == OP_INVOKE_STATIC) {
                hasInterest = methodHasInterest(vsrc1, vdst, interestRegObjMap);
            } else {
                hasInterest = rangeMethodHasInterest(vsrc1, vdst, interestRegObjMap);
            }
            if(!hasInterest) {
                goto finally;
            }
            
            Method* methodToCall;
            if(opcode == OP_INVOKE_SUPER || opcode == OP_INVOKE_SUPER_RANGE) {
                Method* baseMethod;
                baseMethod = dvmDexGetResolvedMethod(methodClassDex, ref);
                if (baseMethod == NULL) {
                    baseMethod = resolveMethod(method->clazz, ref, METHOD_VIRTUAL);
                    if(baseMethod == NULL) { // we should have encountered a wrong version method branch
                        endParse(methodAccInfo, toParse, &executions);
                        continue;
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
                endParse(methodAccInfo, toParse, &executions);
                continue;
            }
            //ALOGE("methodParser parse direct %s.%s, by %s.%s", methodToCall->clazz->descriptor, methodToCall->name, method->clazz->descriptor, method->name);
            MethodAccInfo* subAccInfo = new MethodAccInfo();
            subAccInfo->method = methodToCall;
            // setup subcall method access info and parse
            parseMethod(subAccInfo, chain);
            if(opcode == OP_INVOKE_SUPER || opcode == OP_INVOKE_DIRECT || opcode == OP_INVOKE_STATIC) {
                mergeMethodArgs(vsrc1, vdst, interestRegObjMap, toParse->methodAccInfo, subAccInfo);
            } else {
                mergeRangeMethodArgs(vsrc1, vdst, interestRegObjMap, toParse->methodAccInfo, subAccInfo);
            }
            freeMethodAccInfo(subAccInfo);
            toParse->affectTry = true;
        } else if(opcode == OP_MOVE_RESULT || opcode == OP_MOVE_RESULT_WIDE || opcode == OP_MOVE_EXCEPTION) {
            vdst = inst_aa(insns);
            interestRegObjMap->erase(vdst);
            if(toParse->methodAccInfo->curMethodReturns != NULL) {
                delete toParse->methodAccInfo->curMethodReturns;
                toParse->methodAccInfo->curMethodReturns = NULL;
            }
        } else if(opcode == OP_MOVE_RESULT_OBJECT) {
            vdst = inst_aa(insns);
            // we only process the move result of a method
            if(toParse->lastop == OP_FILLED_NEW_ARRAY || toParse->lastop == OP_FILLED_NEW_ARRAY_RANGE) {
                // in this case, we erase the destination register from the interest interest because we have flagged the object it include as all
                interestRegObjMap->erase(vdst);
                goto finally;
            }
            if(toParse->methodAccInfo->curMethodReturns != NULL) {
                (*interestRegObjMap)[vdst] = *(toParse->methodAccInfo->curMethodReturns);
                delete toParse->methodAccInfo->curMethodReturns;
                toParse->methodAccInfo->curMethodReturns = NULL;
                toParse->affectTry = true;
            } else {
                interestRegObjMap->erase(vdst);
            }
        } else if(opcode == OP_RETURN_VOID || opcode == OP_RETURN || opcode == OP_RETURN_WIDE) {
            // stop the current branch of parsing instruction stream
            endParse(methodAccInfo, toParse, &executions);
            continue;
        } else if(opcode == OP_RETURN_OBJECT) {
            vsrc1 = inst_aa(insns);
            if(interestRegObjMap->find(vsrc1) != interestRegObjMap->end()) {
                if(toParse->methodAccInfo->returnObjs == NULL) {
                    toParse->methodAccInfo->returnObjs = new std::set<ObjectAccInfo*>();
                }
                toParse->methodAccInfo->returnObjs->insert(((*interestRegObjMap)[vsrc1]).begin(), ((*interestRegObjMap)[vsrc1]).end());
            }
            // stop the current branch of parsing instruction stream
            endParse(methodAccInfo, toParse, &executions);
            continue;
        } else if(opcode == OP_IF_EQ || opcode == OP_IF_NE || opcode == OP_IF_LT
            || opcode == OP_IF_GE || opcode == OP_IF_GT || opcode == OP_IF_LE
            || opcode == OP_IF_EQZ || opcode == OP_IF_NEZ || opcode == OP_IF_LTZ
            || opcode == OP_IF_GEZ || opcode == OP_IF_GTZ || opcode == OP_IF_LEZ) {
            branches++;
            int branchOffset = (s2)insns[1];
            // check if the branch will lead to an instruction cycle
            bool isCycle = false;
            int newOffset = currentOffset + branchOffset;
            if(toParse->insOffsets->find(newOffset) != toParse->insOffsets->end()) {
                isCycle = true;
            }
            if(!isCycle) {
                toParse->lastop = opcode;
                ParseInfo* branchParseInfo = new ParseInfo();
                copyParseInfo(toParse, branchParseInfo);
                branchParseInfo->insoff = newOffset;
                executions.insert(branchParseInfo);
            }
            
            // the continuation of the loop will parse the branch not taken
        } else if(opcode == OP_GOTO) {
            vdst = inst_aa(insns);
            width = (s1)vdst;
            // check if the goto will lead to an instruction cycle
            bool isCycle = false;
            int newOffset = currentOffset + width;
            if(toParse->insOffsets->find(newOffset) != toParse->insOffsets->end()) {
                isCycle = true;
            }
            if(isCycle) {
                endParse(methodAccInfo, toParse, &executions);
                continue;
            }
        } else if(opcode == OP_GOTO_16) {
            s4 offset = (s2) insns[1];
            width = offset;
            // check if the goto will lead to an instruction cycle
            bool isCycle = false;
            int newOffset = currentOffset + width;
            if(toParse->insOffsets->find(newOffset) != toParse->insOffsets->end()) {
                isCycle = true;
            }
            if(isCycle) {
                endParse(methodAccInfo, toParse, &executions);
                continue;
            }
        } else if(opcode == OP_GOTO_32) {
            s4 offset = insns[1];               // low-order 16 bits
            offset |= ((s4) insns[2]) << 16;    // high-order 16 bits
            width = offset;
            // check if the goto will lead to an instruction cycle
            bool isCycle = false;
            int newOffset = currentOffset + width;
            if(toParse->insOffsets->find(newOffset) != toParse->insOffsets->end()) {
                isCycle = true;
            }
            if(isCycle) {
                endParse(methodAccInfo, toParse, &executions);
                continue;
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
                if(toParse->insOffsets->find(newOffset) != toParse->insOffsets->end()) {
                    isCycle = true;
                }
                if(!isCycle) {
                    // parse the branch taken
                    toParse->lastop = opcode;
                    ParseInfo* branchParseInfo = new ParseInfo();
                    copyParseInfo(toParse, branchParseInfo);
                    branchParseInfo->insoff = newOffset;
                    executions.insert(branchParseInfo);
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
            endParse(methodAccInfo, toParse, &executions);
            continue;
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
            toParse->affectTry = true;
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
            if(opcode == OP_AGET_OBJECT) {
                ObjectAccInfo* objAccInfo = new ObjectAccInfo();
                objAccInfo->allFlag = true;
                objAccInfo->inArray = true;
                (*interestRegObjMap)[vdst].insert(objAccInfo);
            }
            toParse->affectTry = true;
        } else if(opcode == OP_APUT_OBJECT) {
            vdst = inst_aa(insns);
            flagVecAllArray(&((*interestRegObjMap)[vdst]));
            toParse->affectTry = true;
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
finally:
        toParse->insoff += width;
        toParse->lastop = opcode;
        if(!checkInterest(toParse)) {
            //ALOGE("got opcode with obj not in methodaccinfo, opcode: %d", opcode);
        }
    }
    //ALOGE("method %s.%s has %d branches, catch branches:%d, mergecount: %d", method->clazz->descriptor, method->name, branches, catchBranches, mergecount);
}

int timeuse = 0;
int maxtime = 0;
int maxit = 0;
Method* maxMethod;
int counts = 0;

void parseMethod(MethodAccInfo* methodAccInfo, std::vector<Method*>* chain) {
    Method* method = methodAccInfo->method;
    /*if(strcmp(method->clazz->descriptor, "Ldalvik/system/DexFile;") == 0
            && strcmp(method->name, "<init>") == 0
            && method->idx == 79) {
        ALOGE("offset map has it or not: %d", parsedMethodOffMap->find(method) != parsedMethodOffMap->end());
    }*/
    if(parsedMethodOffMap->find(method) != parsedMethodOffMap->end()) {
        //ALOGE("find a parse result in cache: %s.%s.%d", method->clazz->descriptor, method->name, method->idx);
        struct timeval start, end;
        gettimeofday(&start, NULL);
        ParsedMethoOffInfo* poffInfo = (*parsedMethodOffMap)[method];
        loadStructureInFile(methodAccInfo, poffInfo->offStart, poffInfo->length);
        gettimeofday(&end, NULL);
        timeuse += 1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec;
        if(maxtime < 1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec) {
            maxMethod = method;
            maxit = counts;
        }
        maxtime = (maxtime >= 1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec) ? maxtime : 1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec;
        counts++;
        return;
    } else {
        //ALOGE("missing a parse result in cache: %s.%s.%d", method->clazz->descriptor, method->name, method->idx);
    }
    populateMethodAccInfo(methodAccInfo);
    bool isCycle = false;
    // check if this method makes an invocation cycle, if true, then set all the parameters as need to be migrate all
    for(unsigned int i = 0; i < chain->size(); i++) {
        if(method == chain->at(i)) {
            isCycle = true;
        }
    }
    // a method invocation cycle, an abstract or native method cannot be parsed, then we just set all the parameters as need migration
    if(isCycle || dvmIsNativeMethod(method) || dvmIsAbstractMethod(method)) {
        for(unsigned int idx = 0; idx < methodAccInfo->args->size(); idx++) {
            flagObjAll(methodAccInfo->args->at(idx));
        }
        persistMethodAllInfo(methodAccInfo);
        return;
    }
    chain->push_back(method);
    // declare a map which will contain the list of registers the method should track
    // in each register, we use a vector to track all the possible object this vector might store
    const u2* insns = method->insns;
    //u4 insnsSize = dvmGetMethodInsnsSize(method);
    int depth = 0;
    bool exitMethod = false;
    parseInsns(insns, methodAccInfo, chain, depth, &exitMethod);
    
    chain->pop_back();

    persistMethodAllInfo(methodAccInfo);
}

void depthTraverse(ObjectAccInfo* objAccInfo, int depth) {
    if(objAccInfo->allFlag) {
        //ALOGE("methodParser depth: %d, allFlag is: %d", depth, objAccInfo->allFlag);
        return;
    }
    for(unsigned int i = 0; i < objAccInfo->fieldSet.size(); i++) {
        //ALOGE("methodParser depth: %d, offset: %d, value is: %d", depth, i, objAccInfo->fieldSet[i] != NULL);
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
                //ALOGE("traverse object address: %p", accVector->at(j));
                // will access this field
                frontier.push(&(accVector->at(j)->fieldSet));
                *dstfile << "1";
            } else {
                //ALOGE("traverse object all address: %p", accVector->at(j));
                // will access this field but requires to migrate all
                *dstfile << "2";
            }
        }
        *dstfile << "|";
    }
    *dstfile << std::endl;
}

void persistMethodInfo(MethodAccInfo* methodAccInfo, const char* fileName) {
    std::ofstream dstfile;
    dstfile.open(fileName, std::ios::app);
    Method* method = methodAccInfo->method;
    // output method identification
    dstfile << method->clazz->descriptor << " " << method->name << " " << method->idx << std::endl;
    for(unsigned int i = 0; i < methodAccInfo->args->size(); i++) {
        writeObjAccInfo(methodAccInfo->args->at(i), &dstfile);
        //depthTraverse(methodAccInfo->args->at(i), 0);
    }
    dstfile << std::endl;
    /*for(unsigned int i = 0; i < methodAccInfo->globalClazz->size(); i++) {
        dstfile << methodAccInfo->globalClazz->at(i)->clazz->descriptor << std::endl;
        writeObjAccInfo(methodAccInfo->globalClazz->at(i), &dstfile);
    }
    dstfile << std::endl;*/
    dstfile.close();
}

static void indexObjList(std::queue<ObjectAccInfo*>* frontier, std::vector<ObjectAccInfo*>* objList) {
    int index = objList->size();
    while(!frontier->empty()) {
        ObjectAccInfo* objAccInfo = frontier->front();
        frontier->pop();
        if(objAccInfo->idx >= 0) {
            continue;
        }
        objAccInfo->idx = index++;
        objList->push_back(objAccInfo);
        for(unsigned int i = 0; i < objAccInfo->fieldSet.size(); i++) {
            if(objAccInfo->fieldSet[i] != NULL) {
                frontier->push(objAccInfo->fieldSet[i]);
            }
            if(objAccInfo->trackSet[i] != NULL) {
                for(std::set<ObjectAccInfo*>::iterator it = objAccInfo->trackSet[i]->begin(); it != objAccInfo->trackSet[i]->end(); ++it) {
                    frontier->push(*it);
                }
            }
        }
    }
}

/* set the index no for each objectAccInfo */
static void indexMethodAccInfo(MethodAccInfo* methodAccInfo, std::vector<ObjectAccInfo*>* objList) {
    std::queue<ObjectAccInfo*> frontier;
    for(unsigned int i = 0; i < methodAccInfo->globalClazz->size(); i++) {
        frontier.push(methodAccInfo->globalClazz->at(i));
    }
    for(unsigned int i = 0; i < methodAccInfo->args->size(); i++) {
        frontier.push(methodAccInfo->args->at(i));
    }

    indexObjList(&frontier, objList);
}

static void indexRegObj(std::map<u2, std::set<ObjectAccInfo*> >* interestRegObjMap, std::vector<ObjectAccInfo*>* objList) {
    std::queue<ObjectAccInfo*> frontier;
    for(std::map<u2, std::set<ObjectAccInfo*> >::iterator mapit = interestRegObjMap->begin(); mapit != interestRegObjMap->end(); ++mapit) {
        for(std::set<ObjectAccInfo*>::iterator setit = mapit->second.begin(); setit != mapit->second.end(); ++setit) {
            if(*setit != NULL) {
                if((*setit)->idx == -1) {
                    frontier.push(*setit);
                }
            }
        }
    }

    indexObjList(&frontier, objList);
}

static void clearIndex(std::vector<ObjectAccInfo*>* objList) {
    for(unsigned int i = 0; i < objList->size(); i++) {
        objList->at(i)->idx = -1;
    }
}

static bool checkInterest(ParseInfo* parseInfo) {
    std::vector<ObjectAccInfo*> objList;
    indexMethodAccInfo(parseInfo->methodAccInfo, &objList);
    indexRegObj(parseInfo->interestRegObjMap, &objList);
    for(std::map<u2, std::set<ObjectAccInfo*> >::iterator it = parseInfo->interestRegObjMap->begin(); it != parseInfo->interestRegObjMap->end(); ++it) {
        for(std::set<ObjectAccInfo*>::iterator setit = it->second.begin(); setit != it->second.end(); setit++) {
            if(*setit == NULL) {
                ALOGE("got an error that an reg value is NULL");
                clearIndex(&objList);
                return false;
            }
        }
    }
    clearIndex(&objList);
    return true;
}

static void copyParseInfo(ParseInfo* src, ParseInfo* dst) {
    dst->insoff = src->insoff;
    dst->lastop = src->lastop;
    dst->insOffsets = new std::set<int>(src->insOffsets->begin(), src->insOffsets->end());

    // copy MethodAccInfo
    MethodAccInfo* srcMethAccInfo = src->methodAccInfo;
    MethodAccInfo* dstMethAccInfo = new MethodAccInfo();
    dst->methodAccInfo = dstMethAccInfo;
    dstMethAccInfo->method = srcMethAccInfo->method;
    populateMethodAccInfo(dstMethAccInfo);
    std::vector<ObjectAccInfo*> objList;
    indexMethodAccInfo(srcMethAccInfo, &objList);
    indexRegObj(src->interestRegObjMap, &objList);
    std::vector<ObjectAccInfo*> newObjList;
    unsigned int currIdx = 0;
    if(srcMethAccInfo->globalClazz != NULL) {
        currIdx += srcMethAccInfo->globalClazz->size();
        dstMethAccInfo->globalClazz = new std::vector<ClazzAccInfo*>();
        for(unsigned int i = 0; i < srcMethAccInfo->globalClazz->size(); i++) {
            ClazzAccInfo* clzAccInfo = new ClazzAccInfo();
            newObjList.push_back(clzAccInfo);
            clzAccInfo->clazz = srcMethAccInfo->globalClazz->at(i)->clazz;
            dstMethAccInfo->globalClazz->push_back(clzAccInfo);
        }
    }
    if(srcMethAccInfo->args != NULL) {
        currIdx += srcMethAccInfo->args->size();
        dstMethAccInfo->args = new std::vector<ObjectAccInfo*>();
        for(unsigned int i = 0; i < srcMethAccInfo->args->size(); i++) {
            ObjectAccInfo* objAccInfo = new ObjectAccInfo();
            newObjList.push_back(objAccInfo);
            dstMethAccInfo->args->push_back(objAccInfo);
        }
    }
    for(unsigned int i = currIdx; i < objList.size(); i++) {
        newObjList.push_back(new ObjectAccInfo());
    }

    // fill the structure infomation into the new objects list
    for(unsigned int i = 0; i < objList.size(); i++) {
        ObjectAccInfo* srcAccInfo = objList.at(i);
        ObjectAccInfo* dstAccInfo = newObjList.at(i);
        dstAccInfo->allFlag = srcAccInfo->allFlag;
        dstAccInfo->inArray = srcAccInfo->inArray;
        if(srcAccInfo->belonging != NULL) {
            if(srcAccInfo->belonging->idx != -1) {
                dstAccInfo->belonging = newObjList[srcAccInfo->belonging->idx];
            } else {
                dstAccInfo->belonging = new ObjectAccInfo();
            }
        }
        dstAccInfo->nullBranchFlags.resize(srcAccInfo->fieldSet.size());
        dstAccInfo->fieldSet.resize(srcAccInfo->fieldSet.size());
        dstAccInfo->trackSet.resize(srcAccInfo->trackSet.size());
        for(unsigned int j = 0; j < srcAccInfo->fieldSet.size(); j++) {
            dstAccInfo->nullBranchFlags[j] = srcAccInfo->nullBranchFlags[j];
            if(srcAccInfo->fieldSet[j] != NULL) {
                dstAccInfo->fieldSet[j] = newObjList[srcAccInfo->fieldSet[j]->idx];
            }
            if(srcAccInfo->trackSet[j] != NULL) {
                dstAccInfo->trackSet[j] = new std::set<ObjectAccInfo*>();
                for(std::set<ObjectAccInfo*>::iterator it = srcAccInfo->trackSet[j]->begin(); it != srcAccInfo->trackSet[j]->end(); ++it) {
                    dstAccInfo->trackSet[j]->insert(newObjList[(*it)->idx]);
                }
            }
        }
    }

    // copy interesting register maps
    dst->interestRegObjMap = new std::map<u2, std::set<ObjectAccInfo*> >();
    for(std::map<u2, std::set<ObjectAccInfo*> >::iterator mapit = src->interestRegObjMap->begin(); mapit != src->interestRegObjMap->end(); ++mapit) {
        for(std::set<ObjectAccInfo*>::iterator setit = mapit->second.begin(); setit != mapit->second.end(); ++setit) {
            (*(dst->interestRegObjMap))[mapit->first].insert(newObjList[(*setit)->idx]);
        }
    }

    clearIndex(&objList);
}

/* save ObjectAccInfo with structure */
static void saveStructureToFile(MethodAccInfo* methodAccInfo, std::vector<ObjectAccInfo*>* objList) {
    // output method identification
    presultFileTxt << methodAccInfo->method->clazz->descriptor << " " << methodAccInfo->method->name << " " << methodAccInfo->method->idx << std::endl;
    presultFileTxt << methodAccInfo->globalClazz->size() << " " << methodAccInfo->args->size() << std::endl;
    for(unsigned int i = 0; i < objList->size(); i++) {
        ObjectAccInfo* objAccInfo = objList->at(i);
        presultFileTxt << objAccInfo->idx << " " << objAccInfo->allFlag << " " << objAccInfo->inArray << " ";
        for(unsigned int j = 0; j < objAccInfo->nullBranchFlags.size(); j++) {
            presultFileTxt << objAccInfo->nullBranchFlags[j];
        }
        presultFileTxt << " ";
        for(unsigned int j = 0; j < objAccInfo->fieldSet.size(); j++) {
            if(j != 0) {
                presultFileTxt << '|';
            }
            if(objAccInfo->fieldSet[j] == NULL) {
                presultFileTxt << 0;
            } else {
                presultFileTxt << objAccInfo->fieldSet[j]->idx;
            }
        }
        presultFileTxt << " ";
        for(unsigned int j = 0; j < objAccInfo->trackSet.size(); j++) {
            if(j != 0) {
                presultFileTxt << '|';
            }
            if(objAccInfo->trackSet[j] == NULL) {
                presultFileTxt << 0;
            } else {
                int first = true;
                for(std::set<ObjectAccInfo*>::iterator it = objAccInfo->trackSet[j]->begin(); it != objAccInfo->trackSet[j]->end(); ++it) {
                    if(!first) {
                        presultFileTxt << ',';
                    }
                    presultFileTxt << (*it)->idx;
                    first = false;
                }
            }
        }
        presultFileTxt << " ";
        if(i < methodAccInfo->globalClazz->size()) {
            presultFileTxt << methodAccInfo->globalClazz->at(i)->clazz->descriptor;
        }
        presultFileTxt << std::endl;
    }
}

static void saveStructureToBFile(MethodAccInfo* methodAccInfo, std::vector<ObjectAccInfo*>* objList) {
    std::streampos begin, end, end2;
    presultFile.seekp(0, std::ios::beg);
    begin = presultFile.tellp();
    presultFile.seekp(0, std::ios::end);
    end = presultFile.tellp();
    int offStart = end - begin;
    int objIdxSize = sizeof((ObjectAccInfo *)0)->idx;
    // output method identification
    int clzNameIdx = (*strOffMap)[methodAccInfo->method->clazz->descriptor];
    presultFile.write(reinterpret_cast<char*>(&clzNameIdx), sizeof(clzNameIdx));
    int methNameIdx = (*strOffMap)[methodAccInfo->method->name];
    presultFile.write(reinterpret_cast<char*>(&methNameIdx), sizeof(methNameIdx));
    presultFile.write(reinterpret_cast<char*>(&(methodAccInfo->method->idx)), sizeof(methodAccInfo->method->idx));
    unsigned int clzsize = methodAccInfo->globalClazz->size();
    presultFile.write(reinterpret_cast<char*>(&clzsize), sizeof(clzsize));
    unsigned int argsize = methodAccInfo->args->size();
    presultFile.write(reinterpret_cast<char*>(&argsize), sizeof(argsize));
    unsigned int objsize = objList->size();
    presultFile.write(reinterpret_cast<char*>(&objsize), sizeof(objsize));
    int zero = 0;
    int none = -1;
    for(unsigned int i = 0; i < objList->size(); i++) {
        ObjectAccInfo* objAccInfo = objList->at(i);
        presultFile.write(reinterpret_cast<char*>(&(objAccInfo->idx)), sizeof(objAccInfo->idx));
        presultFile.write(reinterpret_cast<char*>(&(objAccInfo->allFlag)), sizeof(objAccInfo->allFlag));
        presultFile.write(reinterpret_cast<char*>(&(objAccInfo->inArray)), sizeof(objAccInfo->inArray));
        unsigned int fsetsize = objAccInfo->fieldSet.size();
        presultFile.write(reinterpret_cast<char*>(&fsetsize), sizeof(fsetsize));
        for(unsigned int j = 0; j < objAccInfo->nullBranchFlags.size(); j++) {
            bool isnullbranch = objAccInfo->nullBranchFlags[j];
            presultFile.write(reinterpret_cast<char*>(&isnullbranch), sizeof(isnullbranch));
        }
        for(unsigned int j = 0; j < objAccInfo->fieldSet.size(); j++) {
            if(objAccInfo->fieldSet[j] == NULL) {
                presultFile.write(reinterpret_cast<char*>(&none), objIdxSize);
            } else {
                presultFile.write(reinterpret_cast<char*>(&(objAccInfo->fieldSet[j]->idx)), sizeof(objAccInfo->fieldSet[j]->idx));
            }
        }
        for(unsigned int j = 0; j < objAccInfo->trackSet.size(); j++) {
            if(objAccInfo->trackSet[j] == NULL) {
                presultFile.write(reinterpret_cast<char*>(&zero), objIdxSize);
            } else {
                unsigned int tracksize = objAccInfo->trackSet[j]->size();
                presultFile.write(reinterpret_cast<char*>(&tracksize), sizeof(tracksize));
                for(std::set<ObjectAccInfo*>::iterator it = objAccInfo->trackSet[j]->begin(); it != objAccInfo->trackSet[j]->end(); ++it) {
                    presultFile.write(reinterpret_cast<char*>(&((*it)->idx)), sizeof((*it)->idx));
                }
            }
        }
        if(i < methodAccInfo->globalClazz->size()) {
            int gclzNameIdx = (*strOffMap)[methodAccInfo->globalClazz->at(i)->clazz->descriptor];
            presultFile.write(reinterpret_cast<char*>(&gclzNameIdx), sizeof(gclzNameIdx));
        }
    }
    presultFile.seekp(0, std::ios::end);
    end2 = presultFile.tellp();
    int length = end2 - end;
    poffFile.seekp(0, std::ios::end);
    poffFile.write(reinterpret_cast<char*>(&clzNameIdx), sizeof(clzNameIdx));
    poffFile.write(reinterpret_cast<char*>(&methNameIdx), sizeof(methNameIdx));
    poffFile.write(reinterpret_cast<char*>(&(methodAccInfo->method->idx)), sizeof(methodAccInfo->method->idx));
    poffFile.write(reinterpret_cast<char*>(&offStart), sizeof(offStart));
    poffFile.write(reinterpret_cast<char*>(&length), sizeof(length));
    ParsedMethoOffInfo* offInfo = new ParsedMethoOffInfo();
    offInfo->offStart = offStart;
    offInfo->length = length;
    (*parsedMethodOffMap)[methodAccInfo->method] = offInfo;
}

void persistMethodAllInfo(MethodAccInfo* methodAccInfo) {
    std::vector<ObjectAccInfo*> objList;
    indexMethodAccInfo(methodAccInfo, &objList);
    if(0) {
        saveStructureToFile(methodAccInfo, &objList);
    }
    saveStructureToBFile(methodAccInfo, &objList);
}

Method* getMethodFromKey(int clzNameIdx, int methNameIdx, unsigned int methodIdx, std::map<long long, Method*>* idxMethodMap) {
    ClassObject* clazz = dvmLookupClass((*offStrMap)[clzNameIdx], NULL, false);
    const char* methodName = (*offStrMap)[methNameIdx];
    long long methodIdxKey = clzNameIdx;
    methodIdxKey <<= 4;
    methodIdxKey += methodIdx;
    if(idxMethodMap != NULL && idxMethodMap->find(methodIdxKey) != idxMethodMap->end() && strcmp((*idxMethodMap)[methodIdxKey]->clazz->descriptor, clazz->descriptor) == 0
        && strcmp((*idxMethodMap)[methodIdxKey]->name, methodName) == 0 && (*idxMethodMap)[methodIdxKey]->idx == methodIdx) {
        return (*idxMethodMap)[methodIdxKey];
    } else {
        Method* vmethods = clazz->virtualMethods;
        size_t vmethodCount = clazz->virtualMethodCount;
        for(size_t j = 0; j < vmethodCount; j++) {
            Method* method = &vmethods[j];
            if(strcmp(method->name, methodName) == 0 && method->idx == methodIdx) {
                if(idxMethodMap != NULL) {
                    (*idxMethodMap)[methodIdxKey] = method;
                }
                return method;
            }
        }
        Method* dmethods = clazz->directMethods;
        size_t dmethodCount = clazz->directMethodCount;
        for(size_t j = 0; j < dmethodCount; j++) {
            Method* method = &dmethods[j];
            if(strcmp(method->name, methodName) == 0 && method->idx == methodIdx) {
                if(idxMethodMap != NULL) {
                    (*idxMethodMap)[methodIdxKey] = method;
                }
                return method;
            }
        }
    }
    return NULL;
}

void loadParsedMethodOffInfo() {
    std::streampos begin, end;
    poffFile.seekg(0, std::ios::end);
    end = poffFile.tellg();
    poffFile.seekg(0, std::ios::beg);
    begin = poffFile.tellg();
    unsigned int total = end - begin;
    char* readbuffer = new char[total];
    poffFile.read(readbuffer, total);
    char* buffer = readbuffer;
    int leftbytes = total;
    while(leftbytes > 0) {
        int clzNameIdx;
        memcpy(&clzNameIdx, buffer, sizeof(clzNameIdx));
        buffer += sizeof(clzNameIdx);
        leftbytes -= sizeof(clzNameIdx);
        int methNameIdx;
        memcpy(&methNameIdx, buffer, sizeof(methNameIdx));
        buffer += sizeof(methNameIdx);
        leftbytes -= sizeof(methNameIdx);
        unsigned int methodIdx;
        memcpy(&methodIdx, buffer, sizeof(methodIdx));
        buffer += sizeof(methodIdx);
        leftbytes -= sizeof(methodIdx);
        // find the specified method reference
        Method* offmethod = getMethodFromKey(clzNameIdx, methNameIdx, methodIdx, NULL);
        
        int offStart;
        memcpy(&offStart, buffer, sizeof(offStart));
        buffer += sizeof(offStart);
        leftbytes -= sizeof(offStart);
        int length;
        memcpy(&length, buffer, sizeof(length));
        buffer += sizeof(length);
        leftbytes -= sizeof(length);

        ParsedMethoOffInfo* offInfo = new ParsedMethoOffInfo();
        offInfo->offStart = offStart;
        offInfo->length = length;
        (*parsedMethodOffMap)[offmethod] = offInfo;
    }
    ALOGE("parsed method count: %d", parsedMethodOffMap->size());
}

void filterInherited() {
    std::fstream invokedByMethodsFile;
    invokedByMethodsFile.open("/local_scratch/jars/results/invokebymeth.bin");
    std::map<Method*, std::set<Method*>* >* invokedByMethodsMap = new std::map<Method*, std::set<Method*>* >();
    std::map<long long, Method*>* idxMethodMap = new std::map<long long, Method*>();
    std::streampos begin, end;
    invokedByMethodsFile.seekg(0, std::ios::end);
    end = invokedByMethodsFile.tellg();
    invokedByMethodsFile.seekg(0, std::ios::beg);
    begin = invokedByMethodsFile.tellg();
    unsigned int total = end - begin;
    char* readbuffer = new char[total];
    invokedByMethodsFile.read(readbuffer, total);
    char* buffer = readbuffer;
    int leftbytes = total;
    while(leftbytes > 0) {
        int clzNameIdx;
        memcpy(&clzNameIdx, buffer, sizeof(clzNameIdx));
        buffer += sizeof(clzNameIdx);
        leftbytes -= sizeof(clzNameIdx);
        int methNameIdx;
        memcpy(&methNameIdx, buffer, sizeof(methNameIdx));
        buffer += sizeof(methNameIdx);
        leftbytes -= sizeof(methNameIdx);
        unsigned int methodIdx;
        memcpy(&methodIdx, buffer, sizeof(methodIdx));
        buffer += sizeof(methodIdx);
        leftbytes -= sizeof(methodIdx);
        
        // find the specified method reference
        Method* keyMethod = getMethodFromKey(clzNameIdx, methNameIdx, methodIdx, idxMethodMap);
        (*invokedByMethodsMap)[keyMethod] = new std::set<Method*>();
        int methodCount;
        memcpy(&methodCount, buffer, sizeof(methodCount));
        buffer += sizeof(methodCount);
        leftbytes -= sizeof(methodCount);
        for(int i = 0; i < methodCount; i++) {
            int clzNameIdx;
            memcpy(&clzNameIdx, buffer, sizeof(clzNameIdx));
            buffer += sizeof(clzNameIdx);
            leftbytes -= sizeof(clzNameIdx);
            int methNameIdx;
            memcpy(&methNameIdx, buffer, sizeof(methNameIdx));
            buffer += sizeof(methNameIdx);
            leftbytes -= sizeof(methNameIdx);
            unsigned int methodIdx;
            memcpy(&methodIdx, buffer, sizeof(methodIdx));
            buffer += sizeof(methodIdx);
            leftbytes -= sizeof(methodIdx);
            Method* invokeByMethod = getMethodFromKey(clzNameIdx, methNameIdx, methodIdx, idxMethodMap);
            (*invokedByMethodsMap)[keyMethod]->insert(invokeByMethod);
        }
    }
    
    // filter the methods which has been inherited by the application
    DvmDex* pDvmDex;
    pDvmDex = loadedDex[loadedDex.size() - 1];
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
        if(resClass->super == javaLangObject) { // this is a new class defined in the apk, no way for reparse
            continue;
        }
        while(resClass != javaLangObject) {
            // traverse and parse every method in the class, see Object.cpp - findMethodInListByDescriptor
            Method* vmethods = resClass->virtualMethods;
            size_t vmethodCount = resClass->virtualMethodCount;
            for(size_t j = 0; j < vmethodCount; j++) {
                Method* method = &vmethods[j];
                if(invokedByMethodsMap->find(method) == invokedByMethodsMap->end()) {
                    continue;
                }
                std::set<Method*>* methodSet = (*invokedByMethodsMap)[method];
                for (std::set<Method*>::iterator it = methodSet->begin(); it != methodSet->end(); ++it) {
                    Method* invokedByMethod = *it;
                    parsedMethodOffMap->erase(invokedByMethod);
                }
            }
            Method* dmethods = resClass->directMethods;
            size_t dmethodCount = resClass->directMethodCount;
            for(size_t j = 0; j < dmethodCount; j++) {
                Method* method = &dmethods[j];
                if(invokedByMethodsMap->find(method) == invokedByMethodsMap->end()) {
                    continue;
                }
                std::set<Method*>* methodSet = (*invokedByMethodsMap)[method];
                for (std::set<Method*>::iterator it = methodSet->begin(); it != methodSet->end(); ++it) {
                    Method* invokedByMethod = *it;
                    parsedMethodOffMap->erase(invokedByMethod);
                }
            }
            resClass = resClass->super;
        }
    }
    
    for(std::map<Method*, std::set<Method*>* >::iterator it = invokedByMethodsMap->begin(); it != invokedByMethodsMap->end(); ++it) {
        delete it->second;
    }
    delete invokedByMethodsMap;
    delete idxMethodMap;
    delete readbuffer;
    invokedByMethodsFile.close();
}

#define BUFFERSIZE (1 << 20) // 1MB
static void readContent(char** buffer, char** bufferHead, char** bufferEnd, void* field, int size, std::fstream* file, int* length) {
    int bufSize = *bufferEnd - *bufferHead;
    int leftSize = *bufferEnd - *buffer;
    // the buffer doesn't have enough contents to fit in field, read more from file
    if(leftSize < size) {
        char* current = *bufferHead;
        memcpy(current, *buffer, leftSize);
        current += leftSize;
        int readSize = (*length <= (bufSize - leftSize) ? *length : (bufSize - leftSize));
        file->read(current, readSize);
        *length -= readSize;
        *buffer = *bufferHead;
        *bufferEnd = current + readSize;
    }
    // read the actual value to field
    memcpy(field, *buffer, size);
    *buffer += size;
}

void loadStructureInFile(MethodAccInfo* methodAccInfo, int offStart, int length) {
    struct timeval start, end;
    gettimeofday(&start, NULL);
    std::map<int, ObjectAccInfo*> idObjMap;
    presultFile.seekg(offStart, std::ios::beg);
    if(counts == 0) {
        gettimeofday(&end, NULL);
        //ALOGE("seek file content finish time: %d, length: %d", (int) (1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec), length);
        start = end;
    }
    int bufSize = (length <= BUFFERSIZE) ? length : BUFFERSIZE;
    char readbuffer[bufSize];
    presultFile.read(readbuffer, bufSize);
    if(counts == 0) {
        gettimeofday(&end, NULL);
        ALOGE("read file content finish time: %d", (int) (1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec));
        start = end;
    }
    int lengthLeft = length - bufSize;
    char* bufferHead = readbuffer;
    char* bufferEnd = readbuffer + bufSize;
    char* buffer = readbuffer;
    int clzNameIdx;
    readContent(&buffer, &bufferHead, &bufferEnd, &clzNameIdx, sizeof(clzNameIdx), &presultFile, &lengthLeft);
    int methNameIdx;
    readContent(&buffer, &bufferHead, &bufferEnd, &methNameIdx, sizeof(methNameIdx), &presultFile, &lengthLeft);
    unsigned int methodIdx;
    readContent(&buffer, &bufferHead, &bufferEnd, &methodIdx, sizeof(methodIdx), &presultFile, &lengthLeft);
    
    methodAccInfo->args = new std::vector<ObjectAccInfo*>();
    methodAccInfo->globalClazz = new std::vector<ClazzAccInfo*>();
    unsigned int globalClzSize;
    readContent(&buffer, &bufferHead, &bufferEnd, &globalClzSize, sizeof(globalClzSize), &presultFile, &lengthLeft);
    unsigned int argSize;
    readContent(&buffer, &bufferHead, &bufferEnd, &argSize, sizeof(argSize), &presultFile, &lengthLeft);
    unsigned int objSize;
    readContent(&buffer, &bufferHead, &bufferEnd, &objSize, sizeof(objSize), &presultFile, &lengthLeft);
    for(unsigned int i = 0; i < globalClzSize; i++) {
        ClazzAccInfo* clzAccInfo = new ClazzAccInfo();
        idObjMap[i] = clzAccInfo;
    }
    if(counts == 0) {
        gettimeofday(&end, NULL);
        //ALOGE("read clazz finish time: %d", (int) (1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec));
        start = end;
    }
    for(unsigned int i = globalClzSize; i < objSize; i++) {
        ObjectAccInfo* objAccInfo = new ObjectAccInfo();
        idObjMap[i] = objAccInfo;
    }
    for(unsigned int i = 0; i < globalClzSize + argSize; i++) {
        int objIdx;
        readContent(&buffer, &bufferHead, &bufferEnd, &objIdx, sizeof(objIdx), &presultFile, &lengthLeft);
        ObjectAccInfo* objAccInfo = idObjMap[objIdx];
        if(i < globalClzSize) {
            methodAccInfo->globalClazz->push_back((ClazzAccInfo*) objAccInfo);
        } else {
            methodAccInfo->args->push_back(objAccInfo);
        }
        bool allFlag;
        readContent(&buffer, &bufferHead, &bufferEnd, &allFlag, sizeof(allFlag), &presultFile, &lengthLeft);
        objAccInfo->allFlag = allFlag;
        bool inArray;
        readContent(&buffer, &bufferHead, &bufferEnd, &inArray, sizeof(inArray), &presultFile, &lengthLeft);
        objAccInfo->inArray = inArray;
        unsigned int fSetSize;
        readContent(&buffer, &bufferHead, &bufferEnd, &fSetSize, sizeof(fSetSize), &presultFile, &lengthLeft);
        objAccInfo->nullBranchFlags.resize(fSetSize);
        for(unsigned int j = 0; j < fSetSize; j++) {
            bool nullBFlag;
            readContent(&buffer, &bufferHead, &bufferEnd, &nullBFlag, sizeof(nullBFlag), &presultFile, &lengthLeft);
            objAccInfo->nullBranchFlags[j] = nullBFlag;
        }
        objAccInfo->fieldSet.resize(fSetSize);
        for(unsigned int j = 0; j < fSetSize; j++) {
            int fieldIdx;
            readContent(&buffer, &bufferHead, &bufferEnd, &fieldIdx, sizeof(fieldIdx), &presultFile, &lengthLeft);
            if(fieldIdx != -1) {
                if(idObjMap.find(fieldIdx) == idObjMap.end()) {
                    if((unsigned int) fieldIdx < globalClzSize) {
                        ClazzAccInfo* fclzAccInfo = new ClazzAccInfo();
                        idObjMap[fieldIdx] = fclzAccInfo;
                    } else {
                        ObjectAccInfo* fobjAccInfo = new ObjectAccInfo();
                        idObjMap[fieldIdx] = fobjAccInfo;
                    }
                }
                objAccInfo->fieldSet[j] = idObjMap[fieldIdx];
            }
        }
        objAccInfo->trackSet.resize(fSetSize);
        for(unsigned int j = 0; j < fSetSize; j++) {
            unsigned int trackSize;
            readContent(&buffer, &bufferHead, &bufferEnd, &trackSize, sizeof(trackSize), &presultFile, &lengthLeft);
            if(trackSize > 0) {
                objAccInfo->trackSet[j] = new std::set<ObjectAccInfo*>();
            }
            for(unsigned int k = 0; k < trackSize; k++) {
                int trackIdx;
                readContent(&buffer, &bufferHead, &bufferEnd, &trackIdx, sizeof(trackIdx), &presultFile, &lengthLeft);
                if(trackIdx != -1) {
                    if(idObjMap.find(trackIdx) == idObjMap.end()) {
                        if((unsigned int) trackIdx < globalClzSize) {
                            ClazzAccInfo* tclzAccInfo = new ClazzAccInfo();
                            idObjMap[trackIdx] = tclzAccInfo;
                        } else {
                            ObjectAccInfo* tobjAccInfo = new ObjectAccInfo();
                            idObjMap[trackIdx] = tobjAccInfo;
                        }
                    }
                    objAccInfo->trackSet[j]->insert(idObjMap[trackIdx]);
                }
            }
        }
        if(i < globalClzSize) {
            int gclzNameIdx;
            readContent(&buffer, &bufferHead, &bufferEnd, &gclzNameIdx, sizeof(gclzNameIdx), &presultFile, &lengthLeft);
            ((ClazzAccInfo*) objAccInfo)->clazz = dvmLookupClass((*offStrMap)[gclzNameIdx], NULL, false);
        }
    }
    if(counts == 0) {
        gettimeofday(&end, NULL);
        //ALOGE("construct clazz and arguments finish time: %d", (int) (1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec));
        start = end;
    }
    for(unsigned int i = globalClzSize + argSize; i < objSize; i++) {
        int objIdx;
        readContent(&buffer, &bufferHead, &bufferEnd, &objIdx, sizeof(objIdx), &presultFile, &lengthLeft);
        ObjectAccInfo* objAccInfo = idObjMap[objIdx];
        bool allFlag;
        readContent(&buffer, &bufferHead, &bufferEnd, &allFlag, sizeof(allFlag), &presultFile, &lengthLeft);
        objAccInfo->allFlag = allFlag;
        bool inArray;
        readContent(&buffer, &bufferHead, &bufferEnd, &inArray, sizeof(inArray), &presultFile, &lengthLeft);
        objAccInfo->inArray = inArray;
        unsigned int fSetSize;
        readContent(&buffer, &bufferHead, &bufferEnd, &fSetSize, sizeof(fSetSize), &presultFile, &lengthLeft);
        objAccInfo->nullBranchFlags.resize(fSetSize);
        for(unsigned int j = 0; j < fSetSize; j++) {
            bool nullBFlag;
            readContent(&buffer, &bufferHead, &bufferEnd, &nullBFlag, sizeof(nullBFlag), &presultFile, &lengthLeft);
            objAccInfo->nullBranchFlags[j] = nullBFlag;
        }
        objAccInfo->fieldSet.resize(fSetSize);
        for(unsigned int j = 0; j < fSetSize; j++) {
            int fieldIdx;
            readContent(&buffer, &bufferHead, &bufferEnd, &fieldIdx, sizeof(fieldIdx), &presultFile, &lengthLeft);
            if(fieldIdx != -1) {
                if(idObjMap.find(fieldIdx) == idObjMap.end()) {
                    if((unsigned int) fieldIdx < globalClzSize) {
                        ClazzAccInfo* fclzAccInfo = new ClazzAccInfo();
                        idObjMap[fieldIdx] = fclzAccInfo;
                    } else {
                        ObjectAccInfo* fobjAccInfo = new ObjectAccInfo();
                        idObjMap[fieldIdx] = fobjAccInfo;
                    }
                }
                objAccInfo->fieldSet[j] = idObjMap[fieldIdx];
            }
        }
        objAccInfo->trackSet.resize(fSetSize);
        for(unsigned int j = 0; j < fSetSize; j++) {
            unsigned int trackSize;
            readContent(&buffer, &bufferHead, &bufferEnd, &trackSize, sizeof(trackSize), &presultFile, &lengthLeft);
            if(trackSize > 0) {
                objAccInfo->trackSet[j] = new std::set<ObjectAccInfo*>();
            }
            for(unsigned int k = 0; k < trackSize; k++) {
                int trackIdx;
                readContent(&buffer, &bufferHead, &bufferEnd, &trackIdx, sizeof(trackIdx), &presultFile, &lengthLeft);
                if(trackIdx != -1) {
                    if(idObjMap.find(trackIdx) == idObjMap.end()) {
                        if((unsigned int)trackIdx < globalClzSize) {
                            ClazzAccInfo* tclzAccInfo = new ClazzAccInfo();
                            idObjMap[trackIdx] = tclzAccInfo;
                        } else {
                            ObjectAccInfo* tobjAccInfo = new ObjectAccInfo();
                            idObjMap[trackIdx] = tobjAccInfo;
                        }
                    }
                    objAccInfo->trackSet[j]->insert(idObjMap[trackIdx]);
                }
            }
        }
    }
    if(counts == 0) {
        gettimeofday(&end, NULL);
        //ALOGE("construct rests finish time: %d", (int) (1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec));
        start = end;
    }
}

void freeMethodAccInfo(MethodAccInfo* methodAccInfo) {
    std::vector<ObjectAccInfo*> objList;
    indexMethodAccInfo(methodAccInfo, &objList);
    for(unsigned int i = 0; i < objList.size(); i++) {
        ObjectAccInfo* objAccInfo = objList.at(i);
        for(unsigned int j = 0; j < objAccInfo->trackSet.size(); j++) {
            if(objAccInfo->trackSet[j] != NULL) {
                delete objAccInfo->trackSet[j];
            }
        }
        delete objAccInfo;
    }
    if(methodAccInfo->args) {
        delete methodAccInfo->args;
    }
    if(methodAccInfo->globalClazz != NULL) {
        delete methodAccInfo->globalClazz;
    }
    if(methodAccInfo->returnObjs != NULL) {
        delete methodAccInfo->returnObjs;
    }
    if(methodAccInfo->curMethodReturns != NULL) {
        delete methodAccInfo->curMethodReturns;
    }
    delete methodAccInfo;
}

static void freeParseInfo(ParseInfo* parseInfo) {
    freeMethodAccInfo(parseInfo->methodAccInfo);
    delete parseInfo->interestRegObjMap;
    delete parseInfo->insOffsets;
    delete parseInfo;
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

void openFiles(bool reuse) {
    char poffFileName[160];
    strcpy(poffFileName, basePath);
    strcat(poffFileName, "/poff.bin");
    poffFile.open(poffFileName, std::ios::in | std::ios::out | std::ios::trunc | std::ios::binary);
    if(reuse) {
        char poffOrigFileName[160];
        strcpy(poffOrigFileName, basePath);
        strcat(poffOrigFileName, "/bak/poff.bin");
        std::ifstream origPOffFile(poffOrigFileName, std::ios::binary);
        poffFile << origPOffFile.rdbuf();
        origPOffFile.close();
    }

    char presultFileName[160];
    strcpy(presultFileName, basePath);
    strcat(presultFileName, "/presult.bin");
    presultFile.open(presultFileName, std::ios::in | std::ios::out | std::ios::trunc | std::ios::binary);
    if(reuse) {
        char presultOrigFileName[160];
        strcpy(presultOrigFileName, basePath);
        strcat(presultOrigFileName, "/bak/presult.bin");
        std::ifstream origPResultFile(presultOrigFileName, std::ios::binary);
        presultFile << origPResultFile.rdbuf();
        origPResultFile.close();
    }

    char presultFileNameTxt[160];
    strcpy(presultFileNameTxt, basePath);
    strcat(presultFileNameTxt, "/presult.txt");
    presultFileTxt.open(presultFileNameTxt, std::ios::in | std::ios::out | std::ios::app);
}

void closeFiles() {
    poffFile.close();
    presultFile.close();
    presultFileTxt.close();
}

