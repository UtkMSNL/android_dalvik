
#include "Dalvik.h"
#include <iostream>
#include <fstream>
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

void loadApk(char* apkPath, char* flag, int maxSubClass);
ClassPathEntry* processClassPath(const char* pathStr);
