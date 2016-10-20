#include "Dalvik.h"
#include <vector>
#include <map>
#include <queue>
#include <iostream>
#include <fstream>
#include <string>
#include <set>

struct charscomp;

/* structure indicates which fields of object have been accessed */
struct ObjectAccInfo {
    // flag indicates that all the attribute of the object should be marked as accessed to assure correctness
    bool allFlag;
    // flag incates that the object can be accessed from an array
    bool inArray;
    // flag which indicates that this field have a branch involving no access
    std::vector<bool> nullBranchFlags;
    // recursively indicates the fields of the object
    std::vector<ObjectAccInfo*> fieldSet;
    // recursively indicates the current attributes of the object which need to be tracked
    std::vector<std::set<ObjectAccInfo*>* > trackSet;
    // set for merge to be able to save temporary result
    std::vector<std::set<ObjectAccInfo*>* > mergeSet;
    // Object which this field belongs to
    ObjectAccInfo* belonging;
    int idx;
    
    ObjectAccInfo() : allFlag(false), inArray(false), belonging(NULL), idx(-1) {}
};

/* structure indicates which fields of object have been accessed */
struct ClazzAccInfo : ObjectAccInfo {
    // indicate the clazz information
    ClassObject* clazz;
};

/* structure indicates which fields of the method arg have been accessed in the method */
struct MethodAccInfo {
    // the method reference to analyze
    Method* method;
    
    // The object access info of the method's arguments
    std::vector<ObjectAccInfo*>* args;
    
    // The object access Info of the global class object
    std::vector<ClazzAccInfo*>* globalClazz;
    
    // objects which represents the possible returns
    std::set<ObjectAccInfo*>* returnObjs;
    
    // objects which represents the possible returns for the method invocation in parsing
    std::set<ObjectAccInfo*>* curMethodReturns;
};

struct ParseInfo {
    /* indicate if a register change will affect the try / catch parsing */
    bool affectTry;
    
    /* the instruction offset of the current parsing path */
    int insoff;
    
    /* last instruction of the current parsing path */
    Opcode lastop;
    
    /* the instruction offsets along the current parsing path */
    std::set<int>* insOffsets;
    
    /* the interesting register states */
    std::map<u2, std::set<ObjectAccInfo*> >* interestRegObjMap;
    
    /* method access information */
    MethodAccInfo* methodAccInfo;
};

struct ObjectAccResult {
    // flag indicates that all the attribute of the object should be marked as accessed to assure correctness
    bool allFlag;
    // recursively indicates the fields of the object
    std::vector<ObjectAccResult*> fieldSet;
   
    /* Tracks the neccessity of migrating low field indexes. */
    u4 migrate;

    /* Tracks the dirtiness of high field indexes. */
    u4* highbits;
};

/* structure indicates which fields of object have been accessed */
struct ClazzAccResult : ObjectAccResult {
    // indicate the clazz information
    char* clazz;
};

struct MethodAccResult {
    //char* clazzDesc;
    
    //char* methodName;
    
    //u4 idx;
    
    std::vector<ObjectAccResult*>* args;
    
    std::vector<ClazzAccResult*>* globalClazz;
};


void populateMethodAccInfo(MethodAccInfo* methodAccInfo);
void parseMethod(MethodAccInfo* methodAccInfo, std::vector<Method*>* chain);
void depthTraverse(ObjectAccInfo* objAccInfo, int depth);
void freeMethodAccInfo(MethodAccInfo* methodAccInfo);
void persistMethodInfo(MethodAccInfo* methodAccInfo, const char* fileName);
void persistMethodAllInfo(MethodAccInfo* methodAccInfo);
void retrieveMethodInfo(std::map<char*, MethodAccResult*, charscomp>* methodAccMap, const char* fileName);
void depthTraverseResult(ObjectAccResult* objAccResult, int depth);
void openFiles(bool reuse);
void closeFiles();
void loadParsedMethodOffInfo();
void filterInherited();
