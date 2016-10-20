#include "Dalvik.h"
#include "ParserCommon.h"
#include "CustomizedClass.h"
#include <sstream> 
#include <stdio.h>
#include <cstdlib>
#include <time.h>

struct BitsVec;
struct ParsedMethoOffInfo;
extern char* basePath;
extern std::vector<DvmDex*> loadedDex;
extern std::map<const char*, int, charscomp>* strOffMap;
extern std::map<int, const char*>* offStrMap;
static ClassObject* javaLangObject;
static std::fstream poffFile;
static std::fstream presultFile;
static std::map<Method*, ParsedMethoOffInfo*>* parsedMethodOffMap = new std::map<Method*, ParsedMethoOffInfo*>();

struct MethodFrame {
    Method* method;
    const u2* insns;
    int leftSize;
    std::map<ClassObject*, BitsVec*>* clzAccInfo;
    int callerIdx;
};

std::stringstream converter;

/* the dictionary to match the class index and its name in the file */
//std::map<unsigned int, char*>* idxClazzNameDict = new std::map<unsigned int, char*>();
/* the dictionary to match the class name and its index in the file */
//std::map<char*, unsigned int, charscomp>* clazzNameDict = new std::map<char*, unsigned int, charscomp>();
/* to store the offset in the file for a certain method */
std::map<char*, unsigned int, charscomp>* methodClzAccMap = new std::map<char*, unsigned int, charscomp>();

//void scanStatic(Method* method, std::set<Method*>* chain, std::map<ClassObject*, BitsVec*>* methodClzAccInfo);

void freeClazzAccInfoMap(std::map<ClassObject*, BitsVec*>* accMap) {
    for (std::map<ClassObject*, BitsVec*>::iterator it = accMap->begin(); it != accMap->end(); ++it) {
        BitsVec* bitsvec = it->second;
        if(bitsvec->bits != NULL) {
            //ALOGE("bitsvec size is: %d", bitsvec->size);
            free(bitsvec->bits);
        }
        delete bitsvec;
    }
    delete accMap;
}

void persistClzAccInfo(Method* method, std::map<ClassObject*, BitsVec*>* result) {
    std::streampos begin, end, end2;
    presultFile.seekp(0, std::ios::beg);
    begin = presultFile.tellp();
    presultFile.seekp(0, std::ios::end);
    end = presultFile.tellp();
    int offStart = end - begin;
    
    // write out the parsing result information
    int clzNameIdx = (*strOffMap)[method->clazz->descriptor];
    presultFile.write(reinterpret_cast<char*>(&clzNameIdx), sizeof(clzNameIdx));
    int methNameIdx = (*strOffMap)[method->name];
    presultFile.write(reinterpret_cast<char*>(&methNameIdx), sizeof(methNameIdx));
    presultFile.write(reinterpret_cast<char*>(&(method->idx)), sizeof(method->idx));
    unsigned int clzsize = result->size();
    presultFile.write(reinterpret_cast<char*>(&clzsize), sizeof(clzsize));
  
    // output method identification
    for (std::map<ClassObject*, BitsVec*>::iterator it = result->begin(); it != result->end(); ++it) {
        ClassObject* obj = it->first;
        int visitClzNameIdx = (*strOffMap)[obj->descriptor];
        presultFile.write(reinterpret_cast<char*>(&visitClzNameIdx), sizeof(visitClzNameIdx));
        BitsVec* bitsvec = it->second;
        presultFile.write(reinterpret_cast<char*>(&(bitsvec->size)), sizeof(bitsvec->size));
        u4 sz = ((bitsvec->size - 1) >> 5) + 1;
        for(u4 i = 0; i < sz; i++) {
            presultFile.write(reinterpret_cast<char*>(&(bitsvec->bits[i])), sizeof(bitsvec->bits[i]));
        }
    }
    
    // write out the offset information
    presultFile.seekp(0, std::ios::end);
    end2 = presultFile.tellp();
    int length = end2 - end;
    poffFile.seekp(0, std::ios::end);
    poffFile.write(reinterpret_cast<char*>(&clzNameIdx), sizeof(clzNameIdx));
    poffFile.write(reinterpret_cast<char*>(&methNameIdx), sizeof(methNameIdx));
    poffFile.write(reinterpret_cast<char*>(&(method->idx)), sizeof(method->idx));
    poffFile.write(reinterpret_cast<char*>(&offStart), sizeof(offStart));
    poffFile.write(reinterpret_cast<char*>(&length), sizeof(length));
    ParsedMethoOffInfo* offInfo = new ParsedMethoOffInfo();
    offInfo->offStart = offStart;
    offInfo->length = length;
    (*parsedMethodOffMap)[method] = offInfo;
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

static bool firstRetrieve = true;
static int maxtime = 0;
static int totalReadTime = 0;
static int hits = 0;
void retrieveClzAccInfo(int offStart, int length, std::map<ClassObject*, BitsVec*>* result) {
    struct timeval start, end;
    gettimeofday(&start, NULL);
    presultFile.seekg(offStart, std::ios::beg);
    int bufSize = (length <= BUFFERSIZE) ? length : BUFFERSIZE;
    char readbuffer[bufSize];
    presultFile.read(readbuffer, bufSize);
    gettimeofday(&end, NULL);
    if(firstRetrieve) {
        ALOGE("seek file content finish time: %d, length: %d", (int) (1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec) / 1000, length);
        firstRetrieve = false;
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
    unsigned int clzsize;
    readContent(&buffer, &bufferHead, &bufferEnd, &clzsize, sizeof(clzsize), &presultFile, &lengthLeft);
    
    for(unsigned int i = 0; i < clzsize; i++) {
        int visitClzNameIdx;
        readContent(&buffer, &bufferHead, &bufferEnd, &visitClzNameIdx, sizeof(visitClzNameIdx), &presultFile, &lengthLeft);
        ClassObject* resClass = dvmLookupClass((*offStrMap)[visitClzNameIdx], NULL, false);
        BitsVec* bitsvec = new BitsVec();
        unsigned int size;
        readContent(&buffer, &bufferHead, &bufferEnd, &size, sizeof(size), &presultFile, &lengthLeft);
        bitsvec->size = size;
        if(size != 0) {
            u4 sz = ((size - 1) >> 5) + 1;
            bitsvec->bits = (u4*)calloc(sz, 4);
            for(unsigned int j = 0; j < sz; j++) {
                readContent(&buffer, &bufferHead, &bufferEnd, &(bitsvec->bits[j]), sizeof(bitsvec->bits[j]), &presultFile, &lengthLeft);
            }
        }
        (*result)[resClass] = bitsvec;
    }
    
    gettimeofday(&end, NULL);
    totalReadTime += (int) (1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec);
    if((int) (1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec) > maxtime) {
        maxtime = (int) (1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec);
    }
    hits++;
}

void mergeClzAccInfo(std::map<ClassObject*, BitsVec*>* methodClzAccInfo, std::map<ClassObject*, BitsVec*>* clazzAccMap) {
    for (std::map<ClassObject*, BitsVec*>::iterator it = clazzAccMap->begin(); it != clazzAccMap->end(); ++it) {
        if(methodClzAccInfo->find(it->first) == methodClzAccInfo->end()) {
            (*methodClzAccInfo)[it->first] = new BitsVec();
        }
        BitsVec* clazzAccInfo = (*methodClzAccInfo)[it->first];
        BitsVec* subAccInfo = it->second;
        u4 sz = ((subAccInfo->size - 1) >> 5) + 1;
        if(clazzAccInfo->size == 0) {
            u4* newbits = (u4*)calloc(sz, 4);
            clazzAccInfo->bits = newbits;
            clazzAccInfo->size = subAccInfo->size;
        } else {
            u4 srcSz = ((clazzAccInfo->size - 1) >> 5) + 1;
            if(srcSz < sz) {
                u4* newbits = (u4*)calloc(sz, 4);
                if(clazzAccInfo->bits != NULL) {
                    memcpy(newbits, clazzAccInfo->bits, srcSz << 2);
                    free(clazzAccInfo->bits);
                }
                clazzAccInfo->bits = newbits;
            }
            if(clazzAccInfo->size < subAccInfo->size) {
                clazzAccInfo->size = subAccInfo->size;
            }
        }
        for(u4 i = 0; i < sz; i++) {
            clazzAccInfo->bits[i] = clazzAccInfo->bits[i] | subAccInfo->bits[i];
        }
    }
    freeClazzAccInfoMap(clazzAccMap);
}

static Method* getMethodFromKey(int clzNameIdx, int methNameIdx, unsigned int methodIdx, std::map<long long, Method*>* idxMethodMap) {
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

static void loadStaticParsedMethodOffInfo() {
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

        if(dvmIsNativeMethod(offmethod)) {
            continue;
        }
        ClassObject* clazz = dvmLookupClass((*offStrMap)[clzNameIdx], NULL, false);
        if(dvmIsInterfaceClass(clazz)) {
            continue;
        }
        ParsedMethoOffInfo* offInfo = new ParsedMethoOffInfo();
        offInfo->offStart = offStart;
        offInfo->length = length;
        (*parsedMethodOffMap)[offmethod] = offInfo;
    }
    ALOGE("parsed method count: %d", parsedMethodOffMap->size());
}

static void filterInheritedForStatic() {
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

int staticcounts = 0;
int methcounts = 0;
int avoidcounts = 0;
unsigned int MaxSubClassCount = 0;
std::set<Method*> staticparsed;
std::set<ClassObject*> avoidparsed;

void scanStatic(Method* method, std::map<ClassObject*, BitsVec*>* methodClzAccInfo) {
    std::vector<MethodFrame*>* toprocess = new std::vector<MethodFrame*>();
    MethodFrame* frame = new MethodFrame();
    frame->method = method;
    frame->insns = method->insns;
    frame->leftSize = dvmGetMethodInsnsSize(method);
    frame->clzAccInfo = methodClzAccInfo;
    frame->callerIdx = -1;
    toprocess->push_back(frame);
    
    while(!toprocess->empty()) {
        u4 frameIdx = toprocess->size() - 1;
        MethodFrame* curFrame = toprocess->at(frameIdx);
        // check if the current frame is making a cycle
        if((u4)curFrame->leftSize == dvmGetMethodInsnsSize(curFrame->method)) {
            // check this method has been parsed before. If so, merge it to the result
            int callerIdx = curFrame->callerIdx;
            if(parsedMethodOffMap->find(curFrame->method) != parsedMethodOffMap->end()) {
                ParsedMethoOffInfo* poffInfo = (*parsedMethodOffMap)[curFrame->method];
                retrieveClzAccInfo(poffInfo->offStart, poffInfo->length, curFrame->clzAccInfo);
                if(callerIdx != -1) {
                    mergeClzAccInfo(toprocess->at(callerIdx)->clzAccInfo, curFrame->clzAccInfo);
                }
                //ALOGE("parsing current method: %s,%s,%d, time: %d", curFrame->method->clazz->descriptor, curFrame->method->name, curFrame->method->idx, timeuse11);
                toprocess->pop_back();
                delete curFrame;
                continue;
            }
            bool isCycle = false;
            while(callerIdx != -1) {
                MethodFrame* callerFrame = toprocess->at(callerIdx);
                if(callerFrame->method == curFrame->method) {
                    // find a cycle, pop this frame
                    //ALOGE("parsing current method at duplicate: %s,%s,%d at caller: %d", curFrame->method->clazz->descriptor, curFrame->method->name, curFrame->method->idx, callerIdx);
                    toprocess->pop_back();
                    freeClazzAccInfoMap(curFrame->clzAccInfo);
                    delete curFrame;
                    isCycle = true;
                    break;
                } else {
                    callerIdx = callerFrame->callerIdx;
                }
            }
            if(isCycle) {
                continue;
            }
        }
        // check if the current method reaches the end
        if(curFrame->leftSize <= 0) {
            if(parsedMethodOffMap->find(curFrame->method) == parsedMethodOffMap->end()) {
                persistClzAccInfo(curFrame->method, curFrame->clzAccInfo);
                staticcounts++;
            }
            if(curFrame->callerIdx != -1) {
                mergeClzAccInfo(toprocess->at(curFrame->callerIdx)->clzAccInfo, curFrame->clzAccInfo);
            }
            //ALOGE("parsing current method: %s,%s,%d", curFrame->method->clazz->descriptor, curFrame->method->name, curFrame->method->idx);
            toprocess->pop_back();
            delete curFrame;
            continue;
        }

        //ALOGE("process frame size: %u, curFrame: %p", toprocess->size(), curFrame);
        //ALOGE("process frame: %p.%p,%s", curFrame, curFrame->method, curFrame->method->name);
        DvmDex* methodClassDex = curFrame->method->clazz->pDvmDex;
        const u2* insns = curFrame->insns;
        std::map<ClassObject*, BitsVec*>* clzAccInfo = curFrame->clzAccInfo;
        int width = dexGetWidthFromInstruction(insns);
        u4 ref;
        curFrame->leftSize -= width;
        curFrame->insns += width;
        Opcode opcode = dexOpcodeFromCodeUnit(*insns);
        if(opcode == OP_SGET_VOLATILE || opcode == OP_SGET_WIDE_VOLATILE || opcode == OP_SGET_OBJECT_VOLATILE
        || opcode == OP_SGET || opcode == OP_SGET_WIDE || opcode == OP_SGET_OBJECT || opcode == OP_SGET_BOOLEAN
        || opcode == OP_SGET_BYTE || opcode == OP_SGET_CHAR || opcode == OP_SGET_SHORT) {
            ref = insns[1];
            StaticField* sfield = (StaticField*)dvmDexGetResolvedField(methodClassDex, ref);
            if (sfield == NULL) {
                sfield = resolveStaticField(curFrame->method->clazz, ref);
                if(sfield == NULL) { // we should have encountered a wrong version field branch, just ignore
                    continue;
                }
            }
            unsigned int offset = sfield - sfield->clazz->sfields;
            if(clzAccInfo->find(sfield->clazz) == clzAccInfo->end()) {
                (*clzAccInfo)[sfield->clazz] = new BitsVec();
            }
            BitsVec* bitsvec = (*clzAccInfo)[sfield->clazz];
            u4 sz = (offset >> 5) + 1;
            if(bitsvec->size == 0) {
                u4* newbits = (u4*)calloc(sz, 4);
                bitsvec->bits = newbits;
                bitsvec->size = offset + 1;
            } else {
                u4 srcSz = ((bitsvec->size - 1) >> 5) + 1;
                if(srcSz < sz) {
                    u4* newbits = (u4*)calloc(sz, 4);
                    if(bitsvec->bits != NULL) {
                        memcpy(newbits, bitsvec->bits, srcSz << 2);
                        free(bitsvec->bits);
                    }
                    bitsvec->bits = newbits;
                }
                if(bitsvec->size < offset + 1) {
                    bitsvec->size = offset + 1;
                }
            }
            bitsvec->bits[sz - 1] = bitsvec->bits[sz - 1] | (1U << (offset & 0x1F));
        } else if(opcode == OP_INVOKE_VIRTUAL || opcode == OP_INVOKE_VIRTUAL_RANGE) {
                ref = insns[1];             // method ref
            
                int voffset;
                Method* baseMethod;
                baseMethod = dvmDexGetResolvedMethod(methodClassDex, ref);
                if (baseMethod == NULL) {
                    baseMethod = resolveMethod(curFrame->method->clazz, ref, METHOD_VIRTUAL);
                    if(baseMethod == NULL) { // we should have encountered a wrong version method branch, just ignore
                        continue;
                    }
                }
                bool isLangObjectClass = baseMethod->clazz == javaLangObject;
                if(isLangObjectClass) {
                    continue;
                }
                voffset = baseMethod->methodIndex;
                std::vector<ClassObject*>* subclasses = findSubClass(baseMethod->clazz);
                if(subclasses->size() > MaxSubClassCount) {
                    for(unsigned int i = 0; i < subclasses->size(); i++)  {
                        if(avoidparsed.find(subclasses->at(i)) == avoidparsed.end()) {
                            avoidcounts++;
                            avoidparsed.insert(subclasses->at(i));
                        }
                    }
                    continue;
                }
                //ALOGE("call virtual method: %s.%s, size: %u, subclass count: %d", baseMethod->clazz->descriptor, baseMethod->name, toprocess->size(), subclasses->size());
                std::set<Method*> parsedMethod;
                
                for(unsigned int idx = 0; idx < subclasses->size(); idx++) {
                    //ALOGE("subclasses: %p, class: %s, base is: %s", subclasses->at(idx), subclasses->at(idx)->descriptor, baseMethod->clazz->descriptor);
                    Method* methodToCall = subclasses->at(idx)->vtable[voffset];
                    assert(methodToCall != NULL);
                    if(dvmIsNativeMethod(methodToCall)) {
                        continue;
                    }
                    if(parsedMethod.find(methodToCall) != parsedMethod.end()) {
                        continue;
                    } else {
                        parsedMethod.insert(methodToCall);
                    }
                    std::map<ClassObject*, BitsVec*>* tocallClzAccMap = new std::map<ClassObject*, BitsVec*>();
                    MethodFrame* toCallFrame = new MethodFrame();
                    toCallFrame->method = methodToCall;
                    toCallFrame->insns = methodToCall->insns;
                    toCallFrame->leftSize = dvmGetMethodInsnsSize(methodToCall);
                    toCallFrame->clzAccInfo = tocallClzAccMap;
                    toCallFrame->callerIdx = frameIdx;
                    toprocess->push_back(toCallFrame);
                    if(staticparsed.find(methodToCall) == staticparsed.end()) {
                        methcounts++;
                        staticparsed.insert(methodToCall);
                    }
                }
            } else if(opcode == OP_INVOKE_INTERFACE || opcode == OP_INVOKE_INTERFACE_RANGE) { // see Interp.cpp-dvmInterpFindInterfaceMethod
                ref = insns[1];             // method ref 
            
                Method* absMethod;
                absMethod = dvmDexGetResolvedMethod(methodClassDex, ref);
                if (absMethod == NULL) {
                    absMethod = resolveInterfaceMethod(curFrame->method->clazz, ref);
                     if(absMethod == NULL) { // we should have encountered a wrong version method branch, just ignore
                        continue;
                    }
                }
                //ALOGE("call interface method: %s.%s, size: %u", absMethod->clazz->descriptor, absMethod->name, toprocess->size());
                assert(dvmIsAbstractMethod(absMethod));
            
                std::vector<ClassObject*>* implclasses = findImplementClass(absMethod->clazz);
                if(implclasses->size() > MaxSubClassCount) {
                    for(unsigned int i = 0; i < implclasses->size(); i++)  {
                        if(avoidparsed.find(implclasses->at(i)) == avoidparsed.end()) {
                            avoidcounts++;
                            avoidparsed.insert(implclasses->at(i));
                        }
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
                    if(dvmIsNativeMethod(methodToCall)) {
                        continue;
                    }
                    if(parsedMethod.find(methodToCall) != parsedMethod.end()) {
                        continue;
                    } else {
                        parsedMethod.insert(methodToCall);
                    }
                    std::map<ClassObject*, BitsVec*>* tocallClzAccMap = new std::map<ClassObject*, BitsVec*>();
                    MethodFrame* toCallFrame = new MethodFrame();
                    toCallFrame->method = methodToCall;
                    toCallFrame->insns = methodToCall->insns;
                    toCallFrame->leftSize = dvmGetMethodInsnsSize(methodToCall);
                    toCallFrame->clzAccInfo = tocallClzAccMap;
                    toCallFrame->callerIdx = frameIdx;
                    toprocess->push_back(toCallFrame);
                    if(staticparsed.find(methodToCall) == staticparsed.end()) {
                        methcounts++;
                        staticparsed.insert(methodToCall);
                    }
                }
            } else if(opcode == OP_INVOKE_SUPER || opcode == OP_INVOKE_DIRECT || opcode == OP_INVOKE_STATIC 
                || opcode == OP_INVOKE_SUPER_RANGE || opcode == OP_INVOKE_DIRECT_RANGE || opcode == OP_INVOKE_STATIC_RANGE) {
                ref = insns[1];             // method ref 
            
                Method* methodToCall;
                if(opcode == OP_INVOKE_SUPER || opcode == OP_INVOKE_SUPER_RANGE) {
                    Method* baseMethod;
                    baseMethod = dvmDexGetResolvedMethod(methodClassDex, ref);
                    if (baseMethod == NULL) {
                        baseMethod = resolveMethod(curFrame->method->clazz, ref, METHOD_VIRTUAL);
                        if(baseMethod == NULL) { // we should have encountered a wrong version method branch
                            continue;
                        }
                    }
                    assert(baseMethod->methodIndex < curFrame->method->clazz->super->vtableCount);
                    methodToCall = curFrame->method->clazz->super->vtable[baseMethod->methodIndex];
                } else if(opcode == OP_INVOKE_DIRECT || opcode == OP_INVOKE_DIRECT_RANGE) {
                    methodToCall = dvmDexGetResolvedMethod(methodClassDex, ref);
                    if (methodToCall == NULL) {
                        methodToCall = resolveMethod(curFrame->method->clazz, ref, METHOD_DIRECT);
                    }
                } else {
                    methodToCall = dvmDexGetResolvedMethod(methodClassDex, ref);
                    if (methodToCall == NULL) {
                        methodToCall = resolveMethod(curFrame->method->clazz, ref, METHOD_STATIC);
                    }
                } 
                if(methodToCall == NULL) { // we should have encountered a wrong version method branch, just ignore
                    continue;
                }
                if(dvmIsNativeMethod(methodToCall)) {
                    continue;
                }
                //ALOGE("call sds method: %s.%s, size: %u", methodToCall->clazz->descriptor, methodToCall->name, toprocess->size());
                std::map<ClassObject*, BitsVec*>* tocallClzAccMap = new std::map<ClassObject*, BitsVec*>();
                MethodFrame* toCallFrame = new MethodFrame();
                toCallFrame->method = methodToCall;
                toCallFrame->insns = methodToCall->insns;
                toCallFrame->leftSize = dvmGetMethodInsnsSize(methodToCall);
                toCallFrame->clzAccInfo = tocallClzAccMap;
                toCallFrame->callerIdx = frameIdx;
                toprocess->push_back(toCallFrame);
                    if(staticparsed.find(methodToCall) == staticparsed.end()) {
                        methcounts++;
                        staticparsed.insert(methodToCall);
                    }
        }
    }
    delete toprocess;
    //ALOGE("scan end, the size is: %d", methodClzAccInfo->size());
}

void persistResult(std::ofstream* staticfile, std::ofstream* offsetfile, Method* method, std::map<ClassObject*, BitsVec*>* result) {
    std::streampos begin, end;
    staticfile->seekp(0, std::ios::beg);
    begin = staticfile->tellp(); 
    staticfile->seekp(0, std::ios::end);
    end = staticfile->tellp();
    unsigned int offset = end - begin;
    
    const char* clazzName = method->clazz->descriptor;
    const char* methodName = method->name;
    char idxStr[33];
    converter << method->idx;
    converter >> idxStr;
    converter.str("");
    converter.clear();
    char* key = new char[strlen(clazzName) + strlen(methodName) + strlen(idxStr) + 3];
    strcpy(key, clazzName);
    strcat(key, " ");
    strcat(key, methodName);
    strcat(key, " ");
    strcat(key, idxStr);
  
    *offsetfile << key << std::endl;
    *offsetfile << offset << std::endl;
    //ALOGE("offset is: %u, key is: %s", offset, key);
    // output method identification
    *staticfile << key << std::endl;
    for (std::map<ClassObject*, BitsVec*>::iterator it = result->begin(); it != result->end(); ++it) {
        ClassObject* obj = it->first;
        //dstfile << (*clazzNameDict)[obj->descriptor] << std::endl;
        *staticfile << obj->descriptor << std::endl;
        BitsVec* bitsvec = it->second;
        *staticfile << bitsvec->size;
        u4 sz = ((bitsvec->size - 1) >> 5) + 1;
        for(u4 i = 0; i < sz; i++) {
            *staticfile << " " << bitsvec->bits[i];
        }
        *staticfile << std::endl;
    }
    *staticfile << std::endl;
    delete[] key;
}

static void openFilesForStatic(bool reuse) {
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
}

static void closeFilesForStatic() {
    poffFile.close();
    presultFile.close();
}

int totalMethods = 0;
void loadApkStatic(char* apkPath, char* flag, int maxcount) {
    if(maxcount == 0) {
        MaxSubClassCount = INT_MAX;
    } else {
        MaxSubClassCount = maxcount;
    }
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
    /*char outFileName[160];
    char* BASE_PATH = getenv("OFFLOAD_PARSE_CACHE");
    if(BASE_PATH == NULL) {
        BASE_PATH = strdup("/data/data");
    }
    strcpy(outFileName, BASE_PATH);
    strcat(outFileName, "/");
    strcat(outFileName, "dict.txt");
    std::ofstream dstfile;
    dstfile.open(outFileName, std::ios::trunc);
    unsigned int clzIdx = 0;
    char outFileName[160];*/
    for(unsigned int idx = 0; idx < loadedDex.size(); idx++) {
        DvmDex* pDvmDex;
        pDvmDex = loadedDex[idx];
        for(unsigned int i = 0; i < pDvmDex->pHeader->classDefsSize; i++) {
            const DexClassDef pClassDef = pDvmDex->pDexFile->pClassDefs[i];
            ClassObject* resClass;  // this segment is copied from Resolve.cpp - dvmResolveClass()
            const char* className;
            className = dexStringByTypeIdx(pDvmDex->pDexFile, pClassDef.classIdx);
            //(*clazzNameDict)[className] = clzIdx;
            //(*idxClazzNameDict)[clzIdx] = className;
            //dstfile << clzIdx++ << " " << className << endl;
            if(className[0] != '\0' && className[1] == '\0') {
                /* primitive type */
                resClass = dvmFindPrimitiveClass(className[0]);
            } else {
                resClass = customDefineClass(pDvmDex, className, NULL);
                if(strcmp(className, "Ljava/lang/Object;") == 0 && javaLangObject == NULL) {
                    javaLangObject = resClass;
                }
                if(resClass == NULL) {
                    //ALOGE("find unloaded class: %s", className);
                    continue;
                }
            }
        }
    }
    
    const char* BASE_PATH = "/local_scratch/jars/results/static";
    if(BASE_PATH == NULL) {
        BASE_PATH = strdup("/data/data");
    }
    basePath = strdup(BASE_PATH);
    char staticpath[160];
    strcpy(staticpath, BASE_PATH);
    strcat(staticpath, "/staticresult.txt");
    std::ofstream staticfile;
    staticfile.open(staticpath, std::ios::out | std::ios::trunc);
    char offsetpath[160];
    strcpy(offsetpath, BASE_PATH);
    strcat(offsetpath, "/offsetresult.txt");
    std::ofstream offsetfile;
    offsetfile.open(offsetpath, std::ios::out | std::ios::trunc);
    loadStringDict();
    openFilesForStatic(reuse);
    if(!isKernelParse && reuse) {
        loadStaticParsedMethodOffInfo();
        filterInheritedForStatic();
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
            if(resClass == javaLangObject) {
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
                //if(strcmp(method->clazz->descriptor, "Lcom/genina/ads/AdView$8;") == 0
                //    && strcmp(method->name, "onPageFinished") == 0 && method->idx == 5878) {
                //ALOGE("start parse method: %s:%s, %u", method->clazz->descriptor, method->name, method->idx);
                //struct timeval start11, end11;
                //gettimeofday(&start11, NULL);
                std::map<ClassObject*, BitsVec*>* methodClzAccInfo = new std::map<ClassObject*, BitsVec*>();
                scanStatic(method, methodClzAccInfo);
                //persistResult(&staticfile, &offsetfile, method, methodClzAccInfo);
                freeClazzAccInfoMap(methodClzAccInfo);
                totalMethods++;
                    if(staticparsed.find(method) == staticparsed.end()) {
                        methcounts++;
                        staticparsed.insert(method);
                    }
                //gettimeofday(&end11, NULL);
                //int timeuse11 = (1000000 * (end11.tv_sec - start11.tv_sec) + end11.tv_usec - start11.tv_usec);
                //ALOGE("time use for method is: %d", timeuse11);
                //}
            }
            Method* dmethods = resClass->directMethods;
            size_t dmethodCount = resClass->directMethodCount;
            for(size_t j = 0; j < dmethodCount; j++) {
                Method* method = &dmethods[j];
                if(dvmIsNativeMethod(method)) {
                    continue;
                }
                //if(strcmp(method->clazz->descriptor, "Lcom/genina/ads/AdView$8;") == 0
                //    && strcmp(method->name, "onPageFinished") == 0 && method->idx == 5878) {
                //ALOGE("start parse method: %s:%s, %u", method->clazz->descriptor, method->name, method->idx);
                //struct timeval start11, end11;
                //gettimeofday(&start11, NULL);
                std::map<ClassObject*, BitsVec*>* methodClzAccInfo = new std::map<ClassObject*, BitsVec*>();
                scanStatic(method, methodClzAccInfo);
                //persistResult(&staticfile, &offsetfile, method, methodClzAccInfo);
                freeClazzAccInfoMap(methodClzAccInfo);
                totalMethods++;
                    if(staticparsed.find(method) == staticparsed.end()) {
                        methcounts++;
                        staticparsed.insert(method);
                    }
                //gettimeofday(&end11, NULL);
                //int timeuse11 = (1000000 * (end11.tv_sec - start11.tv_sec) + end11.tv_usec - start11.tv_usec);
                //ALOGE("time use for method is: %d", timeuse11);
               // }
            }
        }
    }
    staticfile.close();
    offsetfile.close();
    closeFilesForStatic();
    
    /*char offsetFileName[160];
    strcpy(offsetFileName, BASE_PATH);
    strcat(offsetFileName, "/offset.txt");
    std::ofstream offsetfile;
    offsetfile.open(offsetFileName, std::ios::trunc);
    for (std::map<char*, unsigned int, charscomp>::iterator it = methodClzAccMap->begin(); it != methodClzAccMap->end(); ++it) {
        offsetfile << it->first << std::endl;
        offsetfile << it->second << std::endl;
    }
    offsetfile.close();*/
    gettimeofday(&end, NULL);
    int timeuse = (1000000 * (end.tv_sec - start.tv_sec) + end.tv_usec - start.tv_usec) / 1000;
    ALOGE("persist static methods counts: %d, %d, total time: %d, maxtime: %d, totalReadTime: %d, hits: %d, methcounts: %d, avoidcounts: %d", staticcounts, totalMethods, timeuse, maxtime, totalReadTime, hits, methcounts, avoidcounts);
}

void retrieveOffsetMap(std::map<char*, u4, charscomp>* offsetMap, char* filename) {
    std::ifstream srcfile;
    srcfile.open(filename);
    std::string line;
    while(true) {
        std::getline(srcfile, line);
        if(line.compare("") == 0) {
            break;
        }
        char* methodKey = strdup(line.c_str());
        u4 offset;
        std::getline(srcfile, line);
        converter << line;
        converter >> offset;
        converter.str("");
        converter.clear();
        (*offsetMap)[methodKey] = offset;
    }
    srcfile.close();
}

