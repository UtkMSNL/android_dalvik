#include "Dalvik.h"
#include <vector>
#include <map>
#include <queue>
#include <iostream>
#include <fstream>
#include <string>
#include <set>

void loadApkStatic(char* apkPath, char* flag, int maxcount);
void retrieveOffsetMap(std::map<char*, u4, charscomp>* offsetMap, char* filename);

