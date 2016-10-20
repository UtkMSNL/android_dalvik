#include "Dalvik.h"
#include <vector>
#include <map>
#include <queue>
#include <iostream>
#include <fstream>
#include <string>
#include <set>

struct ParsedMethoOffInfo {
    int offStart;
    int length;
};

struct BitsVec {
    u4* bits;
    u4 size;
};

std::vector<ClassObject*>* findSubClass(ClassObject* clazz);
std::vector<ClassObject*>* findImplementClass(ClassObject* clazz);
ClassObject* resolveClass(const ClassObject* referrer, u4 classIdx, bool fromUnverifiedConstant);
Method* resolveMethod(const ClassObject* referrer, u4 methodIdx, MethodType methodType);
Method* resolveInterfaceMethod(const ClassObject* referrer, u4 methodIdx);
InstField* resolveInstField(const ClassObject* referrer, u4 ifieldIdx);
StaticField* resolveStaticField(const ClassObject* referrer, u4 sfieldIdx);
void loadStringDict();
