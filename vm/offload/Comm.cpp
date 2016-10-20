#include "Dalvik.h"
#include "alloc/HeapInternal.h"
#include <sstream> 

#include <sys/time.h>

#define TIMER_BEGIN()                                                       \
  u8             _end_time_us_;                                             \
  struct timeval _start_time_;                                              \
  struct timeval _end_time_;                                                \
  gettimeofday(&_start_time_, NULL)

#define TIMER_END(threadId, name, bytes, fields)                                      \
  gettimeofday(&_end_time_, NULL);                                          \
  _end_time_us_ = (_end_time_.tv_sec - _start_time_.tv_sec) * 1000000 +     \
                     (_end_time_.tv_usec - _start_time_.tv_usec);           \
  ALOGI("THREAD %d TIMER %s %lld.%06lld [%d bytes, %d fields]", threadId, name,                 \
        _end_time_us_ / 1000000, _end_time_us_ % 1000000,                   \
        (bytes), (fields))

#define TIMER_RESET() \
  gettimeofday(&_start_time_, NULL)

#define READWRITEFUNC(type, size, ntoh, hton)                                 \
  static void write##size(FifoBuffer* fb, type v) {                           \
    v = hton(v);                                                              \
    auxFifoPushData(fb, (char*)&v, sizeof(v));                                \
  }                                                                           \
  static type read##size(FifoBuffer* fb) {                                    \
    type v;                                                                   \
    auxFifoReadBuffer(fb, (char*)&v, sizeof(v));                              \
    return ntoh(v);                                                           \
  }

READWRITEFUNC(u1, U1, , );
READWRITEFUNC(u2, U2, ntohs, htons);
READWRITEFUNC(u4, U4, ntohl, htonl);
READWRITEFUNC(u8, U8, ntohll, htonll);

static std::stringstream converter;
extern std::ifstream staticfile;

static bool isObjectDirty(ObjectInfo* info);
static bool isFieldDirty(ObjectInfo* info, u4 fieldIndex);
static void writeValue(FifoBuffer* fb, char type, JValue* val);
  
static bool isClassObject(Object* obj) {
  return obj->clazz == gDvm.classJavaLangClass;
}

ObjectInfo* offIdObjectInfo(u4 objId) {
  if(objId == COMM_INVALID_ID) return NULL;
  if(GET_ID_NUM(objId) == COMM_CLASS_BID) return &offIdToClass(objId)->offInfo;
  u4 bid = GET_ID_NUM(objId);
  u4 ind = STRIP_ID_MASK(objId);

  ObjectInfo* info = offTableGet(&gDvm.objTables[bid], ind);
  return info && info->obj ? info : NULL;
}

Object* offIdToObject(u4 objId) {
  ObjectInfo* info = offIdObjectInfo(objId);
  return info ? info->obj : NULL;
}

static u4 getMaxFieldIndex(Object* obj) {
  if(isClassObject(obj)) {
    return ((ClassObject*)obj)->sfieldCount;
  } else if(*obj->clazz->descriptor == '[') {
    return ((ArrayObject*)obj)->length;
  } else {
    return (obj->clazz->objectSize - sizeof(Object)) >> 2;
  }
}

static bool addTrackedObjectIdLocked(Object* obj, u4 objId) {
  obj->objId = objId;
  u4 bid = GET_ID_NUM(objId);
  u4 ind = STRIP_ID_MASK(objId);

  /* Put the object into the table. */
  ObjectInfo* info = offTableLockedGet(&gDvm.objTables[bid], ind);
  if(info->obj && info->obj != obj) return false;

  assert(!info->obj);
  u4 maxFields = getMaxFieldIndex(obj);

  info->obj = obj;
  info->dirty = 0;
  info->bits = maxFields > 32 ? (u4*)calloc((maxFields - 1) >> 5, 4)
                              : (u4*)NULL;
  info->isQueued = false;
  info->isVolatileOwner = info->isLockOwner = bid == GET_ID_NUM(gDvm.idMask);
  return true;
}

void offAddTrackedObject(Object* obj) {
  if(isClassObject(obj) &&
     ((ClassObject*)obj)->super != gDvm.classJavaLangReflectProxy) {
    /* We start tracking a class object when it is initialized.  We add it to
     * the write queue to indicate that it was initialized to the other end. */
    ObjectInfo* info = &((ClassObject*)obj)->offInfo;
    if(!info->isQueued) {
      pthread_mutex_lock(&gDvm.offCommLock);
      if(!info->isQueued) {
        info->isQueued = true;
        offAddToWriteQueueLocked(obj);
      }
      pthread_mutex_unlock(&gDvm.offCommLock);
    }
  } else if(obj->objId == COMM_INVALID_ID) {
    /* Otherwise we do the normal process of allocating an object identifier and
     * setting up a data structure for it. */
    pthread_mutex_lock(&gDvm.offCommLock);
    while(!addTrackedObjectIdLocked(obj, ADD_ID_MASK(gDvm.nextId++)));

    u4 maxField = getMaxFieldIndex(obj);
    ObjectInfo* info = offIdObjectInfo(obj->objId);
    memset(&info->dirty, 0xFF, sizeof(info->dirty));
    if(maxField > 32) {
      memset(info->bits, 0xFF, ((maxField - 1) >> 5) << 2);
    }

    if(gDvm.isServer) {
      offAddToWriteQueueLocked(obj);
    }
    pthread_mutex_unlock(&gDvm.offCommLock);
  }
}

void offAddVectorIntoTrack(std::vector<Object*>* objVec, FifoBuffer* fb) {
  for(unsigned int i = 0; i < objVec->size(); i++) {
    Object* obj = objVec->at(i);
    if(obj->objId == COMM_INVALID_ID) {
      pthread_mutex_lock(&gDvm.offCommLock);
      while(!addTrackedObjectIdLocked(obj, ADD_ID_MASK(gDvm.nextId++)));

      u4 maxField = getMaxFieldIndex(obj);
      ObjectInfo* info = offIdObjectInfo(obj->objId);
      memset(&info->dirty, 0xFF, sizeof(info->dirty));
      if(maxField > 32) {
        memset(info->bits, 0xFF, ((maxField - 1) >> 5) << 2);
      }

      pthread_mutex_unlock(&gDvm.offCommLock);
    }
    ObjectInfo* info = offIdObjectInfo(obj->objId);
    // it has been marked as migrate all before, do not need to handle it again
    if(info->isQueued) {
      continue;
    }
    if(!info->isQueued) {
      pthread_mutex_lock(&gDvm.offCommLock);
      info->isQueued = true;
      offAddToWriteQueueLocked(obj);
      pthread_mutex_unlock(&gDvm.offCommLock);
    }
    bool isDirty = isObjectDirty(info);
    u4 maxIndex;
    if(isDirty) {
      // write object info
      /* Write the object definition. */
      JValue valobj; valobj.l = obj;
      writeValue(fb, 'L', &valobj);  
          
      /* Write the dirty bits. */
      maxIndex = getMaxFieldIndex(obj);
      writeU4(fb, info->dirty);
      //ALOGE("offloading send: object id: %d, dirty: %u", obj->objId, info->dirty);
      if(maxIndex > 32) {
        u4 bsz = (maxIndex - 1) >> 5;
        for(u4 j = 0; j < bsz; j++) {
          writeU4(fb, info->bits[j]);
          //ALOGE("offloading send: object id: %d, dirty bits j: %d, value: %u", obj->objId, j, info->bits[j]);
        }
      }
    }
    if(isClassObject(obj)) {
      /* To sync class objects we just write out all of its globals. */
      ClassObject* clazz = (ClassObject*)obj;

      StaticField* fld = clazz->sfields;
      StaticField* efld = fld + clazz->sfieldCount;
      for(; fld != efld; ++fld) {
        if(isFieldDirty(info, fld - clazz->sfields)) {
          writeValue(fb, *fld->signature, (JValue*)&fld->value);
        }
        if(*fld->signature != '[' && *fld->signature != 'L') {
          continue;
        }
        JValue* val = &fld->value;
        Object* fldObj = (Object*) val->l;
        if(fldObj != NULL) {
          objVec->push_back(fldObj);
        }
      }
    } else {
      ClassObject* clazz = obj->clazz;
      if(*clazz->descriptor != '[') {
        /* For normal class objects we write out all the instance fields. */
        for(; clazz; clazz = clazz->super) {
          InstField* fld = clazz->ifields;
          InstField* efld = fld + clazz->ifieldCount;
          for(; fld != efld; ++fld) {
            if(isFieldDirty(info, (fld->byteOffset - sizeof(Object)) >> 2)) {
              writeValue(fb, *fld->signature,
                       (JValue*)(((char*)obj) + fld->byteOffset));
            }
            if(*fld->signature != '[' && *fld->signature != 'L') {
              continue;
            }
            JValue* val = (JValue*) ((char*)obj + fld->byteOffset);
            Object* fldObj = (Object*) val->l;
            if(fldObj != NULL) {
              objVec->push_back(fldObj);
            }
          }
        }
      } else {
        /* For array objects we send the whole array contents for now. */
        ArrayObject* aobj = (ArrayObject*)obj;
        char* contents = (char*)aobj->contents;
        char type = aobj->clazz->descriptor[1];
        u4 typeWidth = auxTypeWidth(type);
        for(u4 j = 0; j < aobj->length; j++, contents += typeWidth) {
          if(isFieldDirty(info, j)) {
            writeValue(fb, aobj->clazz->descriptor[1], (JValue*)contents);
          }
          if(type != '[' && type != 'L') {
            continue;
          }
          JValue* val = (JValue*) contents;
          Object* fldObj = (Object*) val->l;
          if(fldObj != NULL) {
            objVec->push_back(fldObj);
          }
        }
      }
    }
    if(isDirty) {
        info->dirty = 0;
        u4 maxIndex = getMaxFieldIndex(obj);
        if(maxIndex > 32) {
          u4 bsz = (maxIndex - 1) >> 5;
          for(u4 j = 0; j < bsz; j++) {
            info->bits[j] = 0;
          }
        }
      }
    }
}

void offAddObjectIntoTrack(Object* objToAdd, ObjectAccResult* objAccInfoToAdd, FifoBuffer* fb) {
  if(objToAdd == NULL) {
    return;
  }
  std::vector<Object*> objVec;
  objVec.push_back(objToAdd);
  ObjectAccResult flagAllObj;
  flagAllObj.allFlag = true;
  std::vector<ObjectAccResult*> objAccVec;
  if(objAccInfoToAdd != NULL) {
    objAccVec.push_back(objAccInfoToAdd);
  } else {
    objAccVec.push_back(&flagAllObj);
  }
  for(unsigned int i = 0; i < objVec.size(); i++) {
    Object* obj = objVec[i];
    ObjectAccResult* objAccInfo = objAccVec[i];
    if(obj->objId == COMM_INVALID_ID) {
      pthread_mutex_lock(&gDvm.offCommLock);
      while(!addTrackedObjectIdLocked(obj, ADD_ID_MASK(gDvm.nextId++)));

      u4 maxField = getMaxFieldIndex(obj);
      ObjectInfo* info = offIdObjectInfo(obj->objId);
      memset(&info->dirty, 0xFF, sizeof(info->dirty));
      if(maxField > 32) {
        memset(info->bits, 0xFF, ((maxField - 1) >> 5) << 2);
      }

      pthread_mutex_unlock(&gDvm.offCommLock);
    }
    ObjectInfo* info = offIdObjectInfo(obj->objId);
    // it has been marked as migrate all before, do not need to handle it again
    if(info->isQueued) {
      continue;
    }
    if(!objAccInfo->allFlag) { // this indicates we don't need to migrate all the information
      bool isDirty = isObjectDirty(info);
      u4 maxIndex = 0;
      if(isDirty) {
        // write object info
        /* Write the object definition. */
        JValue valobj; valobj.l = obj;
        writeValue(fb, 'L', &valobj);  
          
        /* Write the dirty bits. */
        maxIndex = getMaxFieldIndex(obj);
        writeU4(fb, info->dirty & objAccInfo->migrate);
        //ALOGE("offloading send: object id: %d, dirty: %u", obj->objId, info->dirty & info->migrate);
        if(maxIndex > 32) {
          u4 bsz = (maxIndex - 1) >> 5;
          u4 asz = (objAccInfo->fieldSet.size() - 1) >> 5;
          for(u4 j = 0; j < bsz; j++) {
            if(j < asz) {
              writeU4(fb, info->bits[j] & objAccInfo->highbits[j]);
            } else {
              writeU4(fb, 0);
            }
            //ALOGE("offloading send: object id: %d, dirty bits j: %d, value: %u", obj->objId, j, info->bits[j] & info->highbits[j]);
          }
        }
      }
      if(isClassObject(obj)) {
        /* To sync class objects we just write out all of its globals. */
        ClassObject* clazz = (ClassObject*)obj;
        
        StaticField* fld = clazz->sfields;
        unsigned int count = ((unsigned int) clazz->sfieldCount < objAccInfo->fieldSet.size()) ? clazz->sfieldCount : objAccInfo->fieldSet.size();
        for(unsigned int offset = 0; offset < count; offset++, ++fld) {
          if(objAccInfo->fieldSet[offset] == NULL) {
            continue;
          }
          if(isFieldDirty(info, fld - clazz->sfields)) {
            writeValue(fb, *fld->signature, (JValue*)&fld->value);
          }
          if(*fld->signature != '[' && *fld->signature != 'L') {
            continue;
          }
          JValue* val = &fld->value;
          Object* fldObj = (Object*) val->l;
          if(fldObj != NULL) {
            objVec.push_back(fldObj);
            objAccVec.push_back(objAccInfo->fieldSet[offset]);
          }
        }
      } else {
        ClassObject* clazz = obj->clazz;
        if(*clazz->descriptor != '[') {
          /* For normal class objects we write out all the instance fields. */
          for(; clazz; clazz = clazz->super) {
            InstField* fld = clazz->ifields;
            InstField* efld = fld + clazz->ifieldCount;
            for(; fld != efld; ++fld) {
              unsigned int offset = (fld->byteOffset - sizeof(Object)) >> 2;
              if(objAccInfo->fieldSet.size() <= offset || objAccInfo->fieldSet[offset] == NULL) {
                continue;
              }
              if(isFieldDirty(info, (fld->byteOffset - sizeof(Object)) >> 2)) {
                writeValue(fb, *fld->signature,
                         (JValue*)(((char*)obj) + fld->byteOffset));
              }
              if(*fld->signature != '[' && *fld->signature != 'L') {
                continue;
              }
              JValue* val = (JValue*) ((char*)obj + fld->byteOffset);
              Object* fldObj = (Object*) val->l;
              if(fldObj != NULL) {
                objVec.push_back(fldObj);
                objAccVec.push_back(objAccInfo->fieldSet[offset]);
              }
            }
          }
        } else {
          // For array, the static analysis will only treat it as migrate all or not migrate
          if(!objAccInfo->allFlag) {
            continue;
          }
          /* For array objects we send the whole array contents for now. */
          ArrayObject* aobj = (ArrayObject*)obj;
          char* contents = (char*)aobj->contents;
          char type = aobj->clazz->descriptor[1];
          u4 typeWidth = auxTypeWidth(type);
          for(u4 j = 0; j < aobj->length; j++, contents += typeWidth) {
            if(isFieldDirty(info, j)) {
              writeValue(fb, aobj->clazz->descriptor[1], (JValue*)contents);
            }
            if(type != '[' && type != 'L') {
              continue;
            }
            JValue* val = (JValue*) contents;
            Object* fldObj = (Object*) val->l;
            if(fldObj != NULL) {
              objVec.push_back(fldObj);
              objAccVec.push_back(&flagAllObj);
            }
          }
        }
      }
      if(isDirty) {
        info->dirty = info->dirty & ~objAccInfo->migrate;
        if(maxIndex > 32) {
          u4 maxIndex = getMaxFieldIndex(obj);
          u4 bsz = (maxIndex - 1) >> 5;
          u4 asz = (objAccInfo->fieldSet.size() - 1) >> 5;
          for(u4 j = 0; j < bsz; j++) {
            if(j < asz) {
              info->bits[j] = info->bits[j] & ~objAccInfo->highbits[j];
            }
          }
        }
      }
    } else {
      if(!info->isQueued) {
        pthread_mutex_lock(&gDvm.offCommLock);
        info->isQueued = true;
        offAddToWriteQueueLocked(obj);
        pthread_mutex_unlock(&gDvm.offCommLock);
      }
      bool isDirty = isObjectDirty(info);
      u4 maxIndex = 0;
      if(isDirty) {
        // write object info
        /* Write the object definition. */
        JValue valobj; valobj.l = obj;
        writeValue(fb, 'L', &valobj);  
          
        /* Write the dirty bits. */
        maxIndex = getMaxFieldIndex(obj);
        writeU4(fb, info->dirty);
        //ALOGE("offloading send: object id: %d, dirty: %u", obj->objId, info->dirty);
        if(maxIndex > 32) {
          u4 bsz = (maxIndex - 1) >> 5;
          for(u4 j = 0; j < bsz; j++) {
            writeU4(fb, info->bits[j]);
            //ALOGE("offloading send: object id: %d, dirty bits j: %d, value: %u", obj->objId, j, info->bits[j]);
          }
        }
      }
      if(isClassObject(obj)) {
        /* To sync class objects we just write out all of its globals. */
        ClassObject* clazz = (ClassObject*)obj;

        StaticField* fld = clazz->sfields;
        StaticField* efld = fld + clazz->sfieldCount;
        for(; fld != efld; ++fld) {
          if(isFieldDirty(info, fld - clazz->sfields)) {
            writeValue(fb, *fld->signature, (JValue*)&fld->value);
          }
          if(*fld->signature != '[' && *fld->signature != 'L') {
            continue;
          }
          JValue* val = &fld->value;
          Object* fldObj = (Object*) val->l;
          if(fldObj != NULL) {
            objVec.push_back(fldObj);
            objAccVec.push_back(&flagAllObj);
          }
        }
      } else {
        ClassObject* clazz = obj->clazz;
        if(*clazz->descriptor != '[') {
          /* For normal class objects we write out all the instance fields. */
          for(; clazz; clazz = clazz->super) {
            InstField* fld = clazz->ifields;
            InstField* efld = fld + clazz->ifieldCount;
            for(; fld != efld; ++fld) {
              if(isFieldDirty(info, (fld->byteOffset - sizeof(Object)) >> 2)) {
                writeValue(fb, *fld->signature,
                         (JValue*)(((char*)obj) + fld->byteOffset));
              }
              if(*fld->signature != '[' && *fld->signature != 'L') {
                continue;
              }
              JValue* val = (JValue*) ((char*)obj + fld->byteOffset);
              Object* fldObj = (Object*) val->l;
              if(fldObj != NULL) {
                objVec.push_back(fldObj);
                objAccVec.push_back(&flagAllObj);
              }
            }
          }
        } else {
          /* For array objects we send the whole array contents for now. */
          ArrayObject* aobj = (ArrayObject*)obj;
          char* contents = (char*)aobj->contents;
          char type = aobj->clazz->descriptor[1];
          u4 typeWidth = auxTypeWidth(type);
          for(u4 j = 0; j < aobj->length; j++, contents += typeWidth) {
            if(isFieldDirty(info, j)) {
              writeValue(fb, aobj->clazz->descriptor[1], (JValue*)contents);
            }
            if(type != '[' && type != 'L') {
              continue;
            }
            JValue* val = (JValue*) contents;
            Object* fldObj = (Object*) val->l;
            if(fldObj != NULL) {
              objVec.push_back(fldObj);
              objAccVec.push_back(&flagAllObj);
            }
          }
        }
      }
      if(isDirty) {
        info->dirty = 0;
        if(maxIndex > 32) {
          u4 bsz = (maxIndex - 1) >> 5;
          for(u4 j = 0; j < bsz; j++) {
            info->bits[j] = 0;
          }
        }
      }
    }
  }
}

static int addClazzReachableObj(ClassObject* clazz, void* vfb) {
  if(clazz->status < CLASS_INITIALIZING) {
    return 0;
  }
  FifoBuffer* fb = (FifoBuffer*) vfb;
  offAddObjectIntoTrack(clazz, NULL, fb);
  return 0;
}

void pushAllClazzInfo(FifoBuffer* fb) {
  //u8 starttime = dvmGetRelativeTimeUsec();
  dvmHashForeach(gDvm.loadedClasses, (HashForeachFunc)addClazzReachableObj, fb);
  //u8 endtime = dvmGetRelativeTimeUsec();
  //ALOGE("sync scan class time with scan loaded classes is: %llu", endtime-starttime);
}

void pushClazzInfo(const Method* method, char* key, FifoBuffer* fb) {
  if(gDvm.methodClzOffsetMap->find(key) == gDvm.methodClzOffsetMap->end()) {
   // ALOGE("sync scan class cannot find the specified key, the key is: %s", key);
    pushAllClazzInfo(fb);
    return;
  }
  //u8 starttime = dvmGetRelativeTimeUsec();
  //u4 classCount = 0;
  //u4 actualCount = 0;
  ClassObject* classLoaderClazz = dvmFindSystemClass("Ljava/lang/ClassLoader;");
  InstField* fld,* efld;
  int byteOffset = 0;
  for(fld = classLoaderClazz->ifields, efld = classLoaderClazz->ifields +
    classLoaderClazz->ifieldCount; fld != efld; ++fld) {
    if(!strcmp("parent", fld->name)) {
      byteOffset = fld->byteOffset;
      break;
    }
  }
  //u4 timeusedforfile = 0;
  //u4 timeusedforparse = 0;
  //u4 timeusedforadd = 0;
  //u8 fstart = dvmGetRelativeTimeUsec();
  staticfile.seekg((*gDvm.methodClzOffsetMap)[key]);
  std::string line;
  // read the method name info
  std::getline(staticfile, line);
  //u8 fend = dvmGetRelativeTimeUsec();
 // timeusedforfile+= fend-fstart;
  std::vector<Object*>* objVec = new std::vector<Object*>();
  while(true) {
    //classCount++;
 // u8 fstart = dvmGetRelativeTimeUsec();
    std::getline(staticfile, line);
 // u8 fend = dvmGetRelativeTimeUsec();
  //timeusedforfile+= fend-fstart;
    if(line.compare("") == 0) {
      break;
    }
    Object* classLoader = method->clazz->classLoader;
    ClassObject* clazz;
    do {
      clazz = dvmLookupClass(line.c_str(), classLoader, false);
      if(classLoader == NULL) {
        break;
      }
      JValue* val = (JValue*) ((char*)classLoader + byteOffset);
      classLoader = (Object*) val->l;
    } while(clazz == NULL);
  //fstart = dvmGetRelativeTimeUsec();
    std::getline(staticfile, line);
  //fend = dvmGetRelativeTimeUsec();
  //timeusedforfile+= fend-fstart;
 // u8 pstart = dvmGetRelativeTimeUsec();
    if(clazz != NULL) {
    //  actualCount++;
      converter.str(line);
      u4 size;
      converter >> size;
      //ALOGE("size is %d, size != 0 is %d, clazz is: %s", size, size!=0, clazz->descriptor);
      u4 sz = ((size - 1) >> 5) + 1;
      u4 maxFields = clazz->sfieldCount;
      u4 fsz = (maxFields - 1) >> 5;
      u4 migrate;
      u4* highbits = maxFields > 32 ? (u4*)calloc(fsz, 4) : (u4*)NULL;
      for(u4 i = 0; i < sz; i++) {
        u4 accInfo;
        converter >> accInfo;
        if(i == 0) {
          migrate = accInfo;
        } else {
          highbits[i - 1] = accInfo;
        }
        for(int j = 0; j < 31; j++) {
          if(((accInfo >> j) & 0x1) != 0) {
            StaticField* fld = clazz->sfields + (i * 32 + j);
            if(*fld->signature == '[' || *fld->signature == 'L') {
              JValue* val = &fld->value;
              Object* fldObj = (Object*) val->l;
              if(fldObj != NULL) {
                //offAddObjectIntoTrack(fldObj, NULL);
                objVec->push_back(fldObj);
              }
            }
          }
        }
      }
      converter.str("");
      converter.clear();
      if(!clazz->offInfo.isQueued) {
        pthread_mutex_lock(&gDvm.offCommLock);
        clazz->offInfo.isQueued = true;
        offAddToWriteQueueLocked(clazz);
        pthread_mutex_unlock(&gDvm.offCommLock);
      }
      bool isDirty = isObjectDirty(&clazz->offInfo);
      if(isDirty) {
        // write object info
        /* Write the object definition. */
        JValue valobj; valobj.l = clazz;
        writeValue(fb, 'L', &valobj);  
          
        /* Write the dirty bits. */
        writeU4(fb, clazz->offInfo.dirty & migrate);
        //ALOGE("offloading send: object id: %d, dirty: %u", clazz->objId, clazz->offInfo.dirty & migrate);
        if(maxFields > 32) {
          for(u4 j = 0; j < fsz; j++) {
            writeU4(fb, clazz->offInfo.bits[j] & highbits[j]);
            //ALOGE("offloading send: object id: %d, dirty bits j: %d, value: %u", clazz->objId, j, clazz->offInfo.bits[j] & highbits[j]);
          }
        }
      }

      StaticField* fld = clazz->sfields;
      StaticField* efld = fld + clazz->sfieldCount;
      for(; fld != efld; ++fld) {
        u4 offset = fld - clazz->sfields;
        if(isFieldDirty(&clazz->offInfo, offset)) {
          if((offset < 32 && (((migrate >> offset) & 0x1) != 0))
            || (offset >= 32 && ((highbits[(offset - 32) >> 5] & (1U << (offset & 0x1F))) != 0))) {
            writeValue(fb, *fld->signature, (JValue*)&fld->value);
          }
        }
      }
      if(isDirty) {
        clazz->offInfo.dirty = clazz->offInfo.dirty & ~migrate;
        if(maxFields > 32) {
          for(u4 j = 0; j < fsz; j++) {
            clazz->offInfo.bits[j] = clazz->offInfo.bits[j] & ~highbits[j];
          }
        }
      }
      if(highbits != NULL) {
        free(highbits);
      }
    }
    //u8 pend = dvmGetRelativeTimeUsec();
    //timeusedforparse+= pend-pstart;
  }
 // u8 astart = dvmGetRelativeTimeUsec();
  offAddVectorIntoTrack(objVec, fb);
  //u8 aend = dvmGetRelativeTimeUsec();
 // timeusedforadd += aend - astart;
  delete(objVec);
  //u8 endtime = dvmGetRelativeTimeUsec();
  //ALOGE("sync scan class time with clazz info is: %llu, classCount: %d, actualCount: %d, timeusedforfile: %d, timeusedforparse: %d, timeusedforadd: %d", endtime-starttime, classCount, actualCount, timeusedforfile, timeusedforparse, timeusedforadd);
}

static bool isObjectDirty(ObjectInfo* info) {
  if(info->dirty != 0) {
    return true;
  }
  u4 maxFields = getMaxFieldIndex(info->obj);
  if(maxFields > 32) {
    u4 fsz = (maxFields - 1) >> 5;
    for(u4 i = 0; i < fsz; i++) {
      if(*(info->bits + i) != 0) {
        return true;
      }
    }
  }
  return false;
}

static bool isFieldDirtyRaw(u4 dirty, u4* bits, u4 fieldIndex) {
  if(fieldIndex < 32) {
    return (dirty & 1U << fieldIndex) != 0;
  }
  return (bits[(fieldIndex - 32) >> 5] & (1U << (fieldIndex & 0x1F))) != 0;
}

static bool isFieldDirty(ObjectInfo* info, u4 fieldIndex) {
  return isFieldDirtyRaw(info->dirty, info->bits, fieldIndex);
}

/* Only allowed in sync operations.  Clear a dirty bit.  Intended to be used in
 * syncPull when the other endpoint overwrites something. */
static void clearDirty(ObjectInfo* info, u4 fieldIndex) {
  if(fieldIndex < 32) {
    info->dirty &= ~(1U << fieldIndex);
  } else {
    info->bits[(fieldIndex - 32) >> 5] &= ~(1U << (fieldIndex & 0x1F));
  }
}

static void writeValue(FifoBuffer* fb, char type, JValue* val) {
  switch(type) {
    case 'Z': writeU1(fb, val->z); break;
    case 'B': writeU1(fb, val->b); break;
    case 'C': writeU2(fb, val->c); break;
    case 'S': writeU2(fb, val->s); break;
    case 'F': case 'I': writeU4(fb, val->i); break;
    case 'D': case 'J': writeU8(fb, val->j); break;
    case '[': case 'L': {
      Object* obj = (Object*)val->l;
      if(obj != NULL) {
        u4 objId = auxObjectToId(obj);
        if(objId == COMM_INVALID_ID) {
          offAddTrackedObject(obj);
          objId = auxObjectToId(obj);
        }
        assert(objId != COMM_INVALID_ID);

        writeU4(fb, auxObjectToId((Object*)obj->clazz));
        writeU4(fb, objId);
        /*if(isClassObject(obj)) {        
            ALOGE("write object clazz id: %d, descriptor: %s", auxObjectToId((Object*)obj->clazz), obj->clazz->descriptor);
            ALOGE("write object instance id: %d, descriptor: %s", objId, ((ClassObject*)obj)->descriptor);
        }*/
        if(*obj->clazz->descriptor == '[') {
          ArrayObject* aobj = (ArrayObject*)obj;
          writeU4(fb, aobj->length);
          //ALOGE("write array instance length: %d", aobj->length);
        }
      } else {
        writeU4(fb, COMM_INVALID_ID);
      }
    } break;
    default: assert(0 && "unexpected type");
  }
}

static void readValue(Thread* self, FifoBuffer* fb, char type,
                      JValue* val, bool sgn_extend) {
  switch(type) {
    case 'Z': val->z = readU1(fb); break;
    case 'B': val->b = readU1(fb); break;
    case 'C': val->c = readU2(fb); break;
    case 'S': val->s = readU2(fb); break;
    case 'F': case 'I': val->i = readU4(fb); break;
    case 'D': case 'J': val->j = readU8(fb); break;
    case '[': case 'L': {
      u4 clId = readU4(fb);
      if(clId == COMM_INVALID_ID) {
        val->l = NULL;
      } else {
        ClassObject* clazz = (ClassObject*)offIdToObject(clId);
        assert(clazz->clazz == gDvm.classJavaLangClass);
        u4 objId = readU4(fb);
        u4 arrLength = *clazz->descriptor == '[' ? readU4(fb) : 0;
        /*if(*clazz->descriptor == '[') {
        ALOGE("read array instance length: %d, class descriptor: %s, clId is: %d", arrLength, clazz->descriptor, clId);
        }*/
        Object* obj = offIdToObject(objId);
        /*if(isClassObject(obj)) {
            ALOGE("read object clazz id: %d", clId);
            ALOGE("read object instance id: %d, , descriptor: %s", objId, ((ClassObject*)obj)->descriptor);
        }*/
        if(obj == NULL) {
          if(*clazz->descriptor == '[') {
            obj = (Object*)dvmAllocArrayByClass(clazz, arrLength,
                                                ALLOC_DEFAULT);
            memset(((ArrayObject*)obj)->contents, 0,
                   arrLength * auxTypeWidth(clazz->descriptor[1]));
          } else {
            obj = dvmAllocObject(clazz, ALLOC_DEFAULT);
            memset(((DataObject*)obj)->instanceData, 0,
                   clazz->objectSize - sizeof(Object));
          }
          addTrackedObjectIdLocked(obj, objId);
          dvmReleaseTrackedAlloc(obj, self);
        }
        assert(obj && "failed to allocate object");
        /*if(isClassObject(obj) && ((ClassObject*)obj)->status == 0) {
            ALOGE("find an error obj with a wrong state, clid: %u, cl descriptor: %s, cl state: %d", objId, ((ClassObject*)obj)->descriptor, ((ClassObject*)obj)->status);
        }*/
        val->l = obj;
      }
    } break;
    default: assert(0 && "unexpected type");
  }
  if(sgn_extend) switch(type) {
    case 'B': val->i = val->b; break;
    case 'S': val->i = val->s; break;
    default: break;
  }
}

void offRegisterProxy(ClassObject* clazz, char* str,
                      ClassObject** interfaces, u4 isz) {
  /* We only allow proxies to be created on the client so if we get here it's
   * because we created a mirror proxy and we don't actually want to register it
   * again. */
  if(gDvm.isServer) return;

  offAddTrackedObject(clazz);
  assert(clazz->objId != COMM_INVALID_ID);
  pthread_mutex_lock(&gDvm.offProxyLock);
  u4 ssz = strlen(str);
  writeU4(&gDvm.offProxyFifo, clazz->objId);
  writeU4(&gDvm.offProxyFifo, ssz);
  auxFifoPushData(&gDvm.offProxyFifo, str, ssz);
  writeU4(&gDvm.offProxyFifo, isz);
  while(isz-- > 0) {
    writeU4(&gDvm.offProxyFifo, auxObjectToId(*interfaces++));
  }
  pthread_mutex_unlock(&gDvm.offProxyLock);
}

void expandProxies(FifoBuffer* fb) {
  while(!auxFifoEmpty(fb)) {
    u4 objId = readU4(fb);
    u4 ssz = readU4(fb);
    char* str = (char*)malloc(ssz + 1);
    auxFifoReadBuffer(fb, str, ssz);
    str[ssz] = 0;
    u4 isz = readU4(fb);
    u4 i;

    StringObject* objstr = dvmCreateStringFromCstr(str);
    ArrayObject* interfaces = dvmAllocArrayByClass(
        dvmFindArrayClassForElement(gDvm.classJavaLangClass),
        isz, ALLOC_DEFAULT);
    for(i = 0; i < isz; i++) {
      ((ClassObject**)(void*)interfaces->contents)[i] =
          (ClassObject*)offIdToObject(readU4(fb));
    }

    ClassObject* clazz = dvmGenerateProxyClass(objstr, interfaces, NULL);
    assert(clazz);
    addTrackedObjectIdLocked(clazz, objId);
    dvmReleaseTrackedAlloc((Object*)interfaces, NULL);
    dvmReleaseTrackedAlloc((Object*)objstr, NULL);
  }
}

void offSyncPushDoIfLocal(bool(*before_func)(void*), void* before_arg,
                     void(*after_func)(void*, FifoBuffer*), void* after_arg) {
  Thread* self = dvmThreadSelf();

  TIMER_BEGIN();
  dvmSuspendAllThreads(SUSPEND_FOR_GC);

  if(before_func && !before_func(before_arg)) {
    dvmResumeAllThreads(SUSPEND_FOR_GC);
    return;
  }
  
  /* Send revision header. */
  offWriteU4(self, gDvm.offSendRevision++);

  /* Send over proxy definitions. */
  offWriteU4(self, auxFifoSize(&gDvm.offProxyFifo));
  while(!auxFifoEmpty(&gDvm.offProxyFifo)) {
    u4 bytes = auxFifoGetBufferSize(&gDvm.offProxyFifo);
    offSendMessage(self, auxFifoGetBuffer(&gDvm.offProxyFifo), bytes);
    auxFifoPushData(&gDvm.offProxyFifoAll,
                    auxFifoGetBuffer(&gDvm.offProxyFifo), bytes);
    auxFifoPopBytes(&gDvm.offProxyFifo, bytes);
  }

  u4 i, j;
  FifoBuffer fb = auxFifoCreate();

  /* Send over new class status updates. */
  //ALOGI("gDvm.offStatusUpdate size is: %u", auxVectorSize(&gDvm.offStatusUpdate));
  for(j = 0; j < auxVectorSize(&gDvm.offStatusUpdate); j++) {
    ClassObject* clazz = (ClassObject*)auxVectorGet(&gDvm.offStatusUpdate, j).l;
    //ALOGE("offloading send: clazz id: %d, clazz name: %s", clazz->objId, clazz->descriptor);
    if(clazz->super == gDvm.classJavaLangReflectProxy) {
        continue;
    }

    JValue valobj; valobj.l = clazz;
    writeValue(&fb, 'L', &valobj);
    writeU4(&fb, (u4)clazz->status);
    writeU4(&fb, (u4)clazz->initThreadId);
  }
  auxVectorResize(&gDvm.offStatusUpdate, 0);
  JValue valobj; valobj.l = NULL;
  writeValue(&fb, 'L', &valobj);

  //u8 starttime = dvmGetRelativeTimeUsec();
  /* Send over stack information. */
  FifoBuffer sfb = auxFifoCreate();
  offPushAllStacks(&sfb, &fb);
  /* Terminate the object list. */
  valobj.l = NULL;
  writeValue(&fb, 'L', &valobj);

  /* Clear the dirty bits. */
  for(i = 0; i < auxVectorSize(&gDvm.offWriteQueue); i++) {
    Object* obj = auxVectorGet(&gDvm.offWriteQueue, i).l;
    ObjectInfo* info = offIdObjectInfo(obj->objId);
    info->isQueued = false;
  }
  auxVectorResize(&gDvm.offWriteQueue, 0);
   // u8 endtime1 = dvmGetRelativeTimeUsec();
    //ALOGE("sync scan construct sending data time: %llu", endtime1 - starttime);

  if(after_func) after_func(after_arg, &sfb);
  dvmResumeAllThreads(SUSPEND_FOR_GC);

  /* Actually send over the data.  We need to send the size of the data so that
   * the other endpoint can buffer in the whole thing before suspending the vm.
   */
  u4 total_bytes = auxFifoSize(&fb) + auxFifoSize(&sfb);
  offWriteU4(self, total_bytes);
  while(!auxFifoEmpty(&fb)) {
    u4 bytes = auxFifoGetBufferSize(&fb);
    offSendMessage(self, auxFifoGetBuffer(&fb), bytes);
    auxFifoPopBytes(&fb, bytes);
  }
  auxFifoDestroy(&fb);
  while(!auxFifoEmpty(&sfb)) {
    u4 bytes = auxFifoGetBufferSize(&sfb);
    offSendMessage(self, auxFifoGetBuffer(&sfb), bytes);
    auxFifoPopBytes(&sfb, bytes);
  }
  auxFifoDestroy(&sfb);
    //u8 endtime = dvmGetRelativeTimeUsec();
   // ALOGE("sync scan send data time: %llu", endtime - endtime1);

  /* Send over any loaded dex files.  Usually there is nothing to do here.
   * However if there is work to do it will be done lockstep with the client.
   * We wish to avoid suspending the whole VM for this part of the sync. */
  offPushDexFiles(self);

  /* Wait for the sync to complete. */
  offThreadWaitForResume(self);
  TIMER_END(self->threadId, "syncPush", total_bytes, 0);
  if(gDvm.offSyncTime == 0) {
    gDvm.offSyncTime =  _end_time_us_ / 50;
  } else {
    gDvm.offSyncTime = (15 * gDvm.offSyncTime + _end_time_us_) / 16;
  }
  ++gDvm.offSyncTimeSamples;
}

void offSyncPush() {
  offSyncPushDoIf(NULL, NULL, NULL, NULL);
}

void offSyncPushDoIf(bool(*before_func)(void*), void* before_arg,
                     void(*after_func)(void*, FifoBuffer*), void* after_arg) {
  if(!gDvm.isServer) {
    offSyncPushDoIfLocal(before_func, before_arg, after_func, after_arg);
    return;
  }
  Thread* self = dvmThreadSelf();

  TIMER_BEGIN();
  dvmSuspendAllThreads(SUSPEND_FOR_GC);

  if(before_func && !before_func(before_arg)) {
    dvmResumeAllThreads(SUSPEND_FOR_GC);
    return;
  }
  
  /* Send revision header. */
  offWriteU4(self, gDvm.offSendRevision++);

  /* Send over proxy definitions. */
  offWriteU4(self, auxFifoSize(&gDvm.offProxyFifo));
  while(!auxFifoEmpty(&gDvm.offProxyFifo)) {
    u4 bytes = auxFifoGetBufferSize(&gDvm.offProxyFifo);
    offSendMessage(self, auxFifoGetBuffer(&gDvm.offProxyFifo), bytes);
    auxFifoPushData(&gDvm.offProxyFifoAll,
                    auxFifoGetBuffer(&gDvm.offProxyFifo), bytes);
    auxFifoPopBytes(&gDvm.offProxyFifo, bytes);
  }

  u4 i, j;
  FifoBuffer fb = auxFifoCreate();

  //u8 starttime = dvmGetRelativeTimeUsec();
  /* Send over stack information. */
  FifoBuffer sfb = auxFifoCreate();
  offPushAllStacks(&sfb, &fb);

  /* Send over new class status updates. */
  //ALOGI("gDvm.offStatusUpdate size is: %u", auxVectorSize(&gDvm.offStatusUpdate));
  for(j = 0; j < auxVectorSize(&gDvm.offStatusUpdate); j++) {
    ClassObject* clazz = (ClassObject*)auxVectorGet(&gDvm.offStatusUpdate, j).l;
    //ALOGE("offloading send: clazz id: %d, clazz name: %s", clazz->objId, clazz->descriptor);
    if(clazz->super == gDvm.classJavaLangReflectProxy) {
        continue;
    }

    JValue valobj; valobj.l = clazz;
    writeValue(&fb, 'L', &valobj);
    writeU4(&fb, (u4)clazz->status);
    writeU4(&fb, (u4)clazz->initThreadId);
  }
  auxVectorResize(&gDvm.offStatusUpdate, 0);
  JValue valobj; valobj.l = NULL;
  writeValue(&fb, 'L', &valobj);

  u4 dirty_fields = 0;
  //ALOGI("gDvm.offWriteQueue size is: %u", auxVectorSize(&gDvm.offWriteQueue));
  for(i = 0; i < auxVectorSize(&gDvm.offWriteQueue); i++) {
    Object* obj = auxVectorGet(&gDvm.offWriteQueue, i).l; assert(obj);
    ObjectInfo* info = offIdObjectInfo(obj->objId); assert(info);
    if(!gDvm.isServer && !isObjectDirty(info)) {
      continue;
    }
    //ALOGE("offloading send: object id: %d", obj->objId);

    /* Write the object definition. */
    JValue valobj; valobj.l = obj;
    writeValue(&fb, 'L', &valobj);

    /* Write the dirty bits. */
    u4 maxIndex = getMaxFieldIndex(obj);
      writeU4(&fb, info->dirty);
      //ALOGE("offloading send: object id: %d, dirty: %u, in allFlag", obj->objId, info->dirty);
    if(maxIndex > 32) {
      u4 bsz = (maxIndex - 1) >> 5;
      for(j = 0; j < bsz; j++) info->bits[j] = htonl(info->bits[j]);
      auxFifoPushData(&fb, (char*)info->bits, bsz << 2);
      for(j = 0; j < bsz; j++) {
        info->bits[j] = ntohl(info->bits[j]);
        //ALOGE("offloading send: object id: %d, dirty bits j: %d, value: %u", obj->objId, j, info->bits[j]);
      }
    }

    if(isClassObject(obj)) {
      /* To sync class objects we just write out all of its globals. */
      ClassObject* clazz = (ClassObject*)obj;
      //ALOGE("offloading send: class id: %d, descriptor: %s", obj->objId, clazz->descriptor);

      StaticField* fld = clazz->sfields;
      StaticField* efld = fld + clazz->sfieldCount;
      for(; fld != efld; ++fld) {
        if(isFieldDirty(info, fld - clazz->sfields)) {
          writeValue(&fb, *fld->signature, (JValue*)&fld->value);
          dirty_fields++;
        }
      }
    } else {
      ClassObject* clazz = obj->clazz;
      if(*clazz->descriptor == '[') {
        /* For array objects we send the whole array contents for now. */
        ArrayObject* aobj = (ArrayObject*)obj;
        char* contents = (char*)aobj->contents;
        //ALOGE("offloading send: array id: %d, descriptor: %s", obj->objId, aobj->clazz->descriptor);

        u4 typeWidth = auxTypeWidth(aobj->clazz->descriptor[1]);
        for(j = 0; j < aobj->length; j++, contents += typeWidth) {
          if(isFieldDirty(info, j)) {
            writeValue(&fb, aobj->clazz->descriptor[1], (JValue*)contents);
            dirty_fields++;
          }
        }
      } else {
        /* For normal class objects we write out all the instance fields. */
        //ALOGE("offloading send: object instance id: %d, descriptor: %s", obj->objId, obj->clazz->descriptor);
        for(; clazz; clazz = clazz->super) {
          InstField* fld = clazz->ifields;
          InstField* efld = fld + clazz->ifieldCount;
          for(; fld != efld; ++fld) {
            if(isFieldDirty(info,
               (fld->byteOffset - sizeof(Object)) >> 2)) {
              writeValue(&fb, *fld->signature,
                         (JValue*)(((char*)obj) + fld->byteOffset));
              dirty_fields++;
            }
          }
        }
      }
    }
  }
  /* Terminate the object list. */
  valobj.l = NULL;
  writeValue(&fb, 'L', &valobj);

  /* Clear the dirty bits. */
  for(i = 0; i < auxVectorSize(&gDvm.offWriteQueue); i++) {
    Object* obj = auxVectorGet(&gDvm.offWriteQueue, i).l;
    ObjectInfo* info = offIdObjectInfo(obj->objId);
    info->isQueued = false;

    u4 maxIndex = getMaxFieldIndex(obj);
    info->dirty = 0;
    if(maxIndex > 32) {
      memset(info->bits, 0, ((maxIndex - 1) >> 5) << 2);
    }
  }
  auxVectorResize(&gDvm.offWriteQueue, 0);
    //u8 endtime1 = dvmGetRelativeTimeUsec();
    //ALOGE("sync construct sending data time: %llu", endtime1 - starttime);

  if(after_func) after_func(after_arg, &sfb);
  dvmResumeAllThreads(SUSPEND_FOR_GC);

  /* Actually send over the data.  We need to send the size of the data so that
   * the other endpoint can buffer in the whole thing before suspending the vm.
   */
  u4 total_bytes = auxFifoSize(&fb) + auxFifoSize(&sfb);
  offWriteU4(self, total_bytes);
  while(!auxFifoEmpty(&fb)) {
    u4 bytes = auxFifoGetBufferSize(&fb);
    offSendMessage(self, auxFifoGetBuffer(&fb), bytes);
    auxFifoPopBytes(&fb, bytes);
  }
  auxFifoDestroy(&fb);
  while(!auxFifoEmpty(&sfb)) {
    u4 bytes = auxFifoGetBufferSize(&sfb);
    offSendMessage(self, auxFifoGetBuffer(&sfb), bytes);
    auxFifoPopBytes(&sfb, bytes);
  }
  auxFifoDestroy(&sfb);
    //u8 endtime = dvmGetRelativeTimeUsec();
    //ALOGE("sync send data time: %llu, total bytes: %d", endtime - starttime, total_bytes);

  /* Send over any loaded dex files.  Usually there is nothing to do here.
   * However if there is work to do it will be done lockstep with the client.
   * We wish to avoid suspending the whole VM for this part of the sync. */
  offPushDexFiles(self);

  /* Wait for the sync to complete. */
  offThreadWaitForResume(self);
  TIMER_END(self->threadId, "syncPush", total_bytes, dirty_fields);
  if(gDvm.offSyncTime == 0) {
    gDvm.offSyncTime =  _end_time_us_ / 50;
  } else {
    gDvm.offSyncTime = (15 * gDvm.offSyncTime + _end_time_us_) / 16;
  }
  ++gDvm.offSyncTimeSamples;
}

bool offSyncPull() {
  return offSyncPullDo(NULL, NULL, NULL, NULL);
}

/* This function looks nearly identical to offSyncPush */
bool offSyncPullDo(void(*before_func)(void*), void* before_arg,
                   void(*after_func)(void*, FifoBuffer*), void* after_arg) {
  struct Thread* self = dvmThreadSelf();

  TIMER_BEGIN();

  /* Grab revision header and wait for our turn.  Do this before we suspend the
   * threads so whoever should be pulling next will go ahead. */
  u4 rev = offReadU4(self);

  /* Read in the proxy data if any. */
  u4 bytes;
  FifoBuffer fbproxy = auxFifoCreate();
  bytes = offReadU4(self);
  if(!gDvm.offConnected) return false;
  while(bytes > 0) {
    char cbuf[1024];
    u4 rbytes = bytes < sizeof(cbuf) ? bytes : sizeof(cbuf);
    offReadBuffer(self, cbuf, rbytes);
    auxFifoPushData(&fbproxy, cbuf, rbytes);
    auxFifoPushData(&gDvm.offProxyFifoAll, cbuf, rbytes);
    bytes -= rbytes;
  }

  /* Read in all of the data we need. */
  FifoBuffer fb = auxFifoCreate();
  bytes = offReadU4(self);
  if(!gDvm.offConnected) return false;
  while(bytes > 0) {
    char cbuf[1024];
    u4 rbytes = bytes < sizeof(cbuf) ? bytes : sizeof(cbuf);
    offReadBuffer(self, cbuf, rbytes);
    auxFifoPushData(&fb, cbuf, rbytes);
    bytes -= rbytes;
  }

  u4 total_bytes = auxFifoSize(&fbproxy) + auxFifoSize(&fb);
  TIMER_END(self->threadId, "syncPull [read]", total_bytes, 0);

  /* Load in any dex files.  Usually there is nothing to do here.  This should
   * happen prior to any thread suspension. */
  offPullDexFiles(self);

  /* Wait for our turn to inflate. */
  if((int)(rev - gDvm.offRecvRevision) > 0) {
    ThreadStatus status = dvmChangeStatus(self, THREAD_WAIT);
    pthread_mutex_lock(&gDvm.offCommLock);
    while((int)(rev - gDvm.offRecvRevision) && gDvm.offConnected) {
      pthread_cond_wait(&gDvm.offPullCond, &gDvm.offCommLock);
    }
    pthread_mutex_unlock(&gDvm.offCommLock);
    dvmChangeStatus(self, status);
  }

  if(!gDvm.offConnected) return false;
  /* At this point all of the data has been received successfully so we can
   * perform the sync safetly even if the other endpoint is about to go down. */

  /* Suspend everything.  We need to lock the heap before the suspend so we can
   * be sure that we won't leave a thread working on the heap which will prevent
   * GCs from happening while we sync.  We don't need this requirement when
   * we're pushing however. */
  dvmLockHeap();
  while(gDvm.gcHeap->gcRunning) {
    dvmWaitForConcurrentGcToComplete();
  }
  dvmSuspendAllThreads(SUSPEND_FOR_GC);
  /* disable concurrent gc from here since it might raise a deadlock
   * this happens because when concurrent gc starts, it will grab dvmLockHeap,
   * after it grabs the lock, it will check if it needs to suspend, if so, the gc thread suspends
   * which makes the current allocate threads cannot work
   */
  gDvm.conGcDisabled = true;
  dvmUnlockHeap();
  TIMER_RESET();
  if(before_func) before_func(before_arg);

  expandProxies(&fbproxy);
  auxFifoDestroy(&fbproxy);
  /* Read in new class statuses. */
  for(;;) {
    JValue valobj; readValue(self, &fb, 'L', &valobj, false);
    ClassObject* clazz = (ClassObject*)valobj.l;
    if(clazz == NULL) break;
    //ALOGE("offloading receive: clazz id: %d, clazz name: %s", clazz->objId, clazz->descriptor);

    if(clazz->status < CLASS_INITIALIZING) {
      /* We need to make sure that this class gets linked together and our
       * important register maps get created. */
      dvmDryInitClass(clazz);
    }
    clazz->status = (ClassStatus)readU4(&fb);
    clazz->initThreadId = readU4(&fb);
  }

  u4 j;
  u4* bits = NULL;
  u4 bitsSz = 0;
  u4 dirtyCount = 0;
  for(;;) {
    JValue valobj; readValue(self, &fb, 'L', &valobj, false);
    Object* obj = valobj.l;
    if(obj == NULL) break;
    ObjectInfo* info = offIdObjectInfo(obj->objId);
    //ALOGE("offloading receive: object id: %d, addr: %p", obj->objId, obj);

    /* Read in the dirty bits. */
    u4 maxIndex = getMaxFieldIndex(obj);
    u4 dirty = readU4(&fb);
    //ALOGE("offloading receive: object id: %d, dirty: %u", obj->objId, dirty);
    if(maxIndex > 32) {
      u4 bsz = (maxIndex - 1) >> 5;
      if(bsz > bitsSz) {
        bits = (u4*)realloc(bits, bsz << 2);
        bitsSz = bsz;
      }
      auxFifoReadBuffer(&fb, (char*)bits, bsz << 2);
      for(j = 0; j < bsz; j++) {
        bits[j] = ntohl(bits[j]);
        //ALOGE("offloading receive: object id: %d, dirty bits j: %d, value: %u", obj->objId, j, bits[j]);
      }
    }
    
    if(isClassObject(obj)) {
      ClassObject* clazz = (ClassObject*)obj;
      //ALOGE("offloading receive: class id: %d, descriptor: %s", obj->objId, clazz->descriptor);

      StaticField* fld = clazz->sfields;
      StaticField* efld = fld + clazz->sfieldCount;
      for(; fld != efld; ++fld) {
        u4 fieldIndex = fld - clazz->sfields;
        if(isFieldDirtyRaw(dirty, bits, fieldIndex)) {
          readValue(self, &fb, *fld->signature, (JValue*)&fld->value, true);
          clearDirty(info, fieldIndex);
          dirtyCount++;
        }
      }
    } else {
      ClassObject* clazz = obj->clazz;
      if(*clazz->descriptor == '[') {
        ArrayObject* aobj = (ArrayObject*)obj;
        char* contents = (char*)aobj->contents;
        //ALOGE("offloading receive: array id: %d, descriptor: %s", obj->objId, aobj->clazz->descriptor);

        u4 typeWidth = auxTypeWidth(clazz->descriptor[1]);
        for(j = 0; j < aobj->length; j++, contents += typeWidth) {
          if(isFieldDirtyRaw(dirty, bits, j)) {
            readValue(self, &fb, clazz->descriptor[1],
                      (JValue*)contents, false);
            clearDirty(info, j);
            dirtyCount++;
          }
        }
      } else {
        //ALOGE("offloading receive: object instance id: %d, descriptor: %s", obj->objId, obj->clazz->descriptor);
        for(; clazz; clazz = clazz->super) {
          InstField* fld = clazz->ifields;
          InstField* efld = fld + clazz->ifieldCount;
          for(; fld != efld; ++fld) {
            u4 fieldIndex = (fld->byteOffset - sizeof(Object)) >> 2;
            if(isFieldDirtyRaw(dirty, bits, fieldIndex)) {
              readValue(self, &fb, *fld->signature,
                        (JValue*)(((char*)obj) + fld->byteOffset), true);
              clearDirty(info, fieldIndex);
              dirtyCount++;
            }
          }
        }
      }
    }
  }
  free(bits);

  offPullAllStacks(&fb);
  if(after_func) after_func(after_arg, &fb);        

  assert(auxFifoSize(&fb) == 0);
  auxFifoDestroy(&fb);

  offWriteU1(self, OFF_ACTION_RESUME);
  TIMER_END(self->threadId, "syncPull", total_bytes, dirtyCount);

  pthread_mutex_lock(&gDvm.offCommLock);
  gDvm.offRecvRevision++;
  pthread_cond_broadcast(&gDvm.offPullCond);
  pthread_mutex_unlock(&gDvm.offCommLock);
  // enable concurrent gc again
  gDvm.conGcDisabled = false;
  dvmResumeAllThreads(SUSPEND_FOR_GC);

  return true;
}

/* We only need to do work when we're not making memory for a potential OOM. */
void offGcMarkOffloadRefs(const GcSpec* spec, bool remark) {
  if(!spec->doPreserve) {
    Thread* self = dvmThreadSelf();
ALOGI("STARTING TRIMGC ON %d", self->threadId);
    if(!self->offTrimSignaled) {
      offWriteU1(self, OFF_ACTION_TRIMGC);
    }
    offGcDoTrackTrim();
    return;
  }

  GcMarkContext* ctx = &gDvm.gcHeap->markContext;
  ctx->finger = (void *)ULONG_MAX;

  pthread_mutex_lock(&gDvm.offCommLock);
  u4 i, j;
  for(i = 0; i < sizeof(gDvm.objTables) / sizeof(gDvm.objTables[0]); ++i) {
    u4 sz = offTableSize(&gDvm.objTables[i]);
    for(j = 0; j < sz; ++j) {
      ObjectInfo* info = offTableGet(&gDvm.objTables[i], j);
      if(info && info->obj) {
        dvmMarkObjectOnStack(info->obj, ctx);
      }
    }
  }
  pthread_mutex_unlock(&gDvm.offCommLock);

  offGcMarkDexRefs(remark);
  dvmProcessMarkStack(ctx);
}

void offGcDoTrackTrim() {
  u4 i, j, k;
  u4 iterations;
  GcMarkContext* ctx = &gDvm.gcHeap->markContext;
  Thread* thctx = &gDvm.gcThreadContext;

  ctx->finger = (void *)ULONG_MAX;
  for(iterations = 1; ; iterations++) {
    u4 bv;
    bool work = false;
ALOGI("ITERATION A %d", iterations);

    /* First send over all marked tracked objects in a bit vector. */
    for(i = 0; i < sizeof(gDvm.objTables) / sizeof(gDvm.objTables[0]); ++i) {
      u4 sz = offTableSize(&gDvm.objTables[i]);
      offWriteU4(thctx, sz);
      for(j = 0; j < sz; j += 32) {
        u4 bv = 0;
        for(k = 0; k < 32 && j + k < sz; k++) {
          ObjectInfo* info = offTableGet(&gDvm.objTables[i], j + k);
          if(info && info->obj && dvmIsMarked(info->obj)) {
            bv |= 1U << k;
          }
        }
        offWriteU4(thctx, bv);
      }
    }

ALOGI("ITERATION B %d", iterations);
    /* Now read in the marked tracked objects from the remoted endpoint and mark
     * them. */
    for(i = 0; i < sizeof(gDvm.objTables) / sizeof(gDvm.objTables[0]); ++i) {
      u4 sz = offReadU4(thctx);
      for(j = 0; j < sz; j += 32) {
        bv = offReadU4(thctx);
        for(k = 0; k < 32 && j + k < sz; k++) {
          if(~bv & 1U << k) continue;

          ObjectInfo* info = offTableGet(&gDvm.objTables[i], j + k);
          if(info && info->obj && !dvmIsMarked(info->obj)) {
            work = true;
            dvmMarkObjectOnStack(info->obj, ctx);
          }
        }
      }
    }

ALOGI("ITERATION C %d %d", iterations, work);
    offWriteU1(thctx, work);
    work |= offReadU1(thctx);
ALOGI("ITERATION D %d %d", iterations, work);
    if(work) {
      dvmProcessMarkStack(ctx);
    } else {
      break;
    }
ALOGI("ITERATION E %d", iterations);
  }

  /* Ok now we can trim all of the objects that haven't been marked. */
  u4 trimmed = 0;
  u4 total = 0;
  for(i = 0; i < sizeof(gDvm.objTables) / sizeof(gDvm.objTables[0]); ++i) {
    u4 sz = offTableSize(&gDvm.objTables[i]);
    for(j = 0; j < sz; ++j) {
      ObjectInfo* info = offTableGet(&gDvm.objTables[i], j);
      if(info && info->obj && !dvmIsMarked(info->obj)) {
        trimmed++;
        info->obj->objId = COMM_INVALID_ID;
        info->obj = NULL;
        free(info->bits);
        info->bits = NULL;
      }
    }
    total += sz;
  }

  u4 purged = 0;
  u4 sz = auxVectorSize(&gDvm.offWriteQueue);
  for(i = 0; i < sz; i++) {
    Object* obj = auxVectorGet(&gDvm.offWriteQueue, i).l;
    if(!dvmIsMarked(obj)) {
      purged++;
      auxVectorSet(&gDvm.offWriteQueue, i--,
          auxVectorGet(&gDvm.offWriteQueue, --sz));
    }
  }
  auxVectorResize(&gDvm.offWriteQueue, sz);

  gDvm.nextId = 0;
  ALOGI("GC_TRACK_TRIM: Trimmed %d/%d objects in %d iterations "
        "purging %d objects from the write queue",
        trimmed, total, iterations, purged);
}

bool offCommStartup() {
  gDvm.conGcDisabled = false;
  gDvm.nextId = 0;
  gDvm.idMask = gDvm.isServer ? 1U << 30 : 0;
  memset(gDvm.objTables, 0, sizeof(gDvm.objTables));
  pthread_mutex_init(&gDvm.offCommLock, NULL);
  pthread_cond_init(&gDvm.offPullCond, NULL);
  gDvm.offWriteQueue = auxVectorCreate(0);
  gDvm.offRecvRevision = gDvm.offSendRevision = 0;
  pthread_mutex_init(&gDvm.offProxyLock, NULL);
  gDvm.offProxyFifo = auxFifoCreate();
  gDvm.offProxyFifoAll = auxFifoCreate();
  gDvm.offStatusUpdate = auxVectorCreate(0);
  return true;
}

void offCommShutdown() {
  u4 i;
  pthread_mutex_destroy(&gDvm.offCommLock);
  for(i = 0; i < sizeof(gDvm.objTables) / sizeof(gDvm.objTables[0]); ++i) {
    offTableDestroy(&gDvm.objTables[i]);
  }
  auxVectorDestroy(&gDvm.offWriteQueue);
}

/* Special native files to add tracking code.

native/java_lang_System.c: OK
UtfString.c: OK
InlineNative.c: OK
Exception.c: OK
Debugger.c: OK
Ddm.c: OK

Jni.c: Still need to make GetArrayElements and GetPrimitiveArrayCritical copying
*/
