#include "Dalvik.h"
#include <sstream> 

//#define SYNC_STACK_ONLY

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

static std::stringstream converter;
extern std::ifstream staticfile;
    
READWRITEFUNC(u1, U1, , );
//READWRITEFUNC(u2, U2, ntohs, htons);
READWRITEFUNC(u4, U4, ntohl, htonl);
READWRITEFUNC(u8, U8, ntohll, htonll);

void offPushAllStacks(FifoBuffer* sfb, FifoBuffer* fb) {
  Thread* thread;
  /*for(thread = gDvm.threadList; thread; thread = thread->next) {
    if(thread->offLocal && !thread->offGhost) {
      offPushStack(sfb, thread);
    }
  }*/
  /* Push strategy for debugging.  We need to revert to the old strategy before
   * we can get failure recovery. */

  thread = dvmThreadSelf();
  if(thread->offLocal && !thread->offGhost) {
    offPushStack(sfb, fb, thread);
  }
  
  writeU4(sfb, (u4)-1);
}

void offPullAllStacks(FifoBuffer* sfb) {
  u4 tid;
  for(tid = readU4(sfb); tid != (u4)-1; tid = readU4(sfb)) {
    offPullStack(sfb, tid);
  }
}

static bool isParamObject(Method* method, int param) {
  int ind = param + (dvmIsStaticMethod(method) ? 1 : 0);
  return ind == 0 || method->shorty[ind] == 'L';
}

static bool isParamLong(Method* method, int param) {
  int ind = param + (dvmIsStaticMethod(method) ? 1 : 0);
  return ind != 0 && (method->shorty[ind] == 'J' ||
                      method->shorty[ind] == 'D');
}

/* Modified by Yong, for the local case, we only migrate one stack frame for method-level offloading */
void offPushStackLocalMethodStart(FifoBuffer* sfb, FifoBuffer* fb, Thread* thread) {
  //u8 beforestarttime = dvmGetRelativeTimeUsec();
  InterpSaveState* sst = &thread->interpSave;
  writeU4(sfb, thread->threadId);
  writeU1(sfb, thread->interrupted);

  if(thread->threadObj) {
    offAddObjectIntoTrack(thread->threadObj, NULL, fb);
  }
  if(thread->exception) {
    offAddObjectIntoTrack(thread->exception, NULL, fb);
  }
  writeU4(sfb, auxObjectToId(thread->threadObj));
  writeU4(sfb, auxObjectToId(thread->exception));
  offTransmitMonitors(thread, sfb);
  //u8 beforetranstime = dvmGetRelativeTimeUsec();
  //ALOGE("sync scan time after transmit locks: %llu", beforetranstime - beforestarttime);

  if(!gDvm.isServer && thread->offLocalOnly) {
    writeU4(sfb, 0);
    writeU4(sfb, 0);
    writeU4(sfb, (u4)-1);
    return;
  }
    
/*
#ifdef SYNC_STACK_ONLY
  assert(0 && "not supported yet");
  void* fp = gDvm.isServer || thread == dvmThreadSelf() ?
        thread->curFrame : NULL;
#else
*/
  u4* fp = sst->curFrame;
  u4 stackOffset;
  if(fp == NULL) {
    stackOffset = 0U;
  } else {
    const StackSaveArea* saveArea = SAVEAREA_FROM_FP(fp);
    u4* prevFp = saveArea->prevFrame;
    thread->offStackFpStop = prevFp;
    if(prevFp == NULL) {
        stackOffset = (thread->interpStackStart - (u1*)fp) + sizeof(StackSaveArea);
    } else {
        stackOffset = (u1*)prevFp - (u1*)fp + (thread->breakFrames * sizeof(StackSaveArea));
    }
  }
  writeU4(sfb, stackOffset); // stack offset
  writeU4(sfb, thread->breakFrames); // thread->breakFrames

  const StackSaveArea* saveArea = SAVEAREA_FROM_FP(fp);
  Method* method = (Method*)saveArea->method;

  // Since we are doing method-level offloading, we would not offload break frame or native method to remote
  /* Otherwise write out the method and pc first. */
  int addr = saveArea->xtra.currentPc - method->insns;
  writeU4(sfb, method->clazz->pDvmDex->id << 24 |
              PACK_METHOD_IDX(method));
  writeU4(sfb, addr);

  /* Then transmit the stack information. */
  const RegisterMap* pMap = dvmGetExpandedRegisterMap(method);
  const u1* regVector = pMap ? dvmRegisterMapGetLine(pMap, addr) : NULL;
  if(regVector == NULL) {
    ALOGE("MISSING REGMAPS %s %s", method->clazz->descriptor, method->name);
  }
  assert(method->clazz->status >= CLASS_INITIALIZING);
  assert(regVector && "No register maps found");
 // u8 beforeendtime = dvmGetRelativeTimeUsec();
 // ALOGE("sync scan time before parsing global: %llu", beforeendtime - beforestarttime);
  
//ALOGI("SENDING %s %s %d", method->clazz->descriptor, method->name, addr);
  const char* clazzName = method->clazz->descriptor;
  const char* methodName = method->name;
  converter << method->idx;
  char* idxStr = strdup(converter.str().c_str());
  converter.str("");
  converter.clear();
  char* key = new char[strlen(clazzName) + strlen(methodName) + strlen(idxStr) + 3];
  strcpy(key, clazzName);
  strcat(key, " ");
  strcat(key, methodName);
  strcat(key, " ");
  strcat(key, idxStr);
  int cfbsizebefore = auxFifoSize(fb);
  pushClazzInfo(method, key, fb);
  int cfbsizeafter = auxFifoSize(fb);
  ALOGE("push stack object size class is: %d", (cfbsizeafter - cfbsizebefore));
  MethodAccResult* methodAccResult = (*gDvm.methodAccMap)[key];
  free(idxStr);
  delete[] key;
  int i;
  int argStart = method->registersSize - method->insSize;
//          ALOGE("value of i is: %d, regsize is: %d", i, method->registersSize);
  u2 bits = 1 << 1;
  const u4* framePtr = (const u4*)fp;
  //framePtr += i;
  //regVector += i / 8;
  //bits = (*regVector++ | 0x100) >> (i % 8);
  //bits <<= 1;
  //u8 starttime = dvmGetRelativeTimeUsec();
  int fbsizebefore = auxFifoSize(fb);
  for(i = 0; i < method->registersSize; i++) {
    u4 rval = *framePtr++;

    bits >>= 1;
    if(bits == 1) {
      bits = *regVector++ | 0x100;
    }

    if(i >= argStart) {
      if(bits & 0x01) {
        /* Register is a non-null object. */
        Object* obj = (Object*)rval;
        if(obj) {
          ObjectAccResult* objAccInfo = NULL;
          if(methodAccResult != NULL && methodAccResult->args->size() == method->insSize) {
            ALOGI("sync scan find the method access info at method start");
            objAccInfo = methodAccResult->args->at(i - argStart);
          }
          //ALOGE("offloading stack for args: %d, objAccInfo is: %p, methodAccResult is: %p", i - argStart, objAccInfo, methodAccResult);
          //if(objAccInfo != NULL) {
         //   ALOGE("offloading stack for args: %d, objAccInfo allFlag is: %d", i - argStart, objAccInfo->allFlag);
          //}
          offAddObjectIntoTrack(obj, objAccInfo, fb);
          //offAddObjectIntoTrack(obj, NULL, false);
        }
        rval = auxObjectToId(obj);
      }
      //ALOGE("offloading send: for i: %d id: %d", i, rval);
      writeU4(sfb, rval);
    } else {
      //ALOGE("offloading send: for i: %d id: %d", i, COMM_INVALID_ID);
      writeU4(sfb, COMM_INVALID_ID);
    }
  }
  int fbsizeafter = auxFifoSize(fb);
  ALOGE("push stack object size is: %d", (fbsizeafter - fbsizebefore));
    //u8 endtime = dvmGetRelativeTimeUsec();
    //ALOGE("sync scan stack time: %llu", endtime - starttime);
    
  dvmReleaseRegisterMapLine(pMap, regVector);
  // write the count of break frames to server
  for(u4 i = 0; i < thread->breakFrames; i++) {
    writeU4(sfb, 0);
  }
  writeU4(sfb, (u4)-1);
  // TODO: What's this used for?
  //thread->offSyncStackStop = sst->curFrame ?
  //    SAVEAREA_FROM_FP(sst->curFrame)->prevFrame : NULL;
}

void offPushStackLocalInMethod(FifoBuffer* sfb, FifoBuffer* fb, Thread* thread) {
  InterpSaveState* sst = &thread->interpSave;
  writeU4(sfb, thread->threadId);
  writeU1(sfb, thread->interrupted);

  if(thread->threadObj) {
    offAddObjectIntoTrack(thread->threadObj, NULL, fb);
  }
  if(thread->exception) {
    offAddObjectIntoTrack(thread->exception, NULL, fb);
  }
  writeU4(sfb, auxObjectToId(thread->threadObj));
  writeU4(sfb, auxObjectToId(thread->exception));
  offTransmitMonitors(thread, sfb);

  if(!gDvm.isServer && thread->offLocalOnly) {
    writeU4(sfb, 0);
    writeU4(sfb, 0);
    writeU4(sfb, (u4)-1);
    return;
  }
    
/*
#ifdef SYNC_STACK_ONLY
  assert(0 && "not supported yet");
  void* fp = gDvm.isServer || thread == dvmThreadSelf() ?
        thread->curFrame : NULL;
#else
*/
  u4* fp = sst->curFrame;
  u4 stackOffset;
  u4 breakIncluded = 0;
  if(fp == NULL) {
    stackOffset = 0U;
  } else {
    // check if thread->offStackFpStop is still valid
    bool stopIsValid = false;
    while(fp != NULL) {
      if(fp == thread->offStackFpStop) {
        stopIsValid = true;
        break;
      }
      const StackSaveArea* saveArea = SAVEAREA_FROM_FP(fp);
      fp = saveArea->prevFrame;
    }
    fp = sst->curFrame;
    if(stopIsValid) {
      const StackSaveArea* stopSaveArea = SAVEAREA_FROM_FP(thread->offStackFpStop);
      const char* clazzName = stopSaveArea->method->clazz->descriptor;
      const char* methodName = stopSaveArea->method->name;
      converter << stopSaveArea->method->idx;
      char* idxStr = strdup(converter.str().c_str());
      converter.str("");
      converter.clear();
      char* key = new char[strlen(clazzName) + strlen(methodName) + strlen(idxStr) + 3];
      strcpy(key, clazzName);
      strcat(key, " ");
      strcat(key, methodName);
      strcat(key, " ");
      strcat(key, idxStr);
      pushClazzInfo(stopSaveArea->method, key, fb);
      free(idxStr);
      delete[] key;
      while(fp != thread->offStackFpStop) {
        if(dvmIsBreakFrame(fp)) {
          breakIncluded++;
        }
        const StackSaveArea* saveArea = SAVEAREA_FROM_FP(fp);
        fp = saveArea->prevFrame;
      }
      fp = sst->curFrame;
      stackOffset = (u1*)thread->offStackFpStop - (u1*)fp + ((thread->breakFrames - breakIncluded) * sizeof(StackSaveArea)); //TODO: might be wrong, see if we need to add or subtract another sizeof(StackSaveArea)
    } else {
      pushAllClazzInfo(fb);
      thread->offStackFpStop = NULL;
      breakIncluded = thread->breakFrames;
      stackOffset = (thread->interpStackStart - (u1*)fp) + sizeof(StackSaveArea);
    }
  }
  writeU4(sfb, stackOffset); // stack offset
  writeU4(sfb, thread->breakFrames); // thread->breakFrames

  while(fp != thread->offStackFpStop && fp != NULL) {
    const StackSaveArea* saveArea = SAVEAREA_FROM_FP(fp);
    Method* method = (Method*)saveArea->method;

    if(dvmIsBreakFrame(fp)) {
      /* Just write the invalid method id to indicate break frame. */
      writeU4(sfb, 0);
    } else if(dvmIsNativeMethod(method)) {
      writeU4(sfb, method->clazz->pDvmDex->id << 24 |
                  PACK_METHOD_IDX(method));
      writeU8(sfb, (u8)(uintptr_t)saveArea->xtra.localRefCookie);

      if(saveArea->prevFrame &&
         SAVEAREA_FROM_FP(saveArea->prevFrame)->method == method) {
        writeU1(sfb, 0);
      } else {
        writeU1(sfb, 1);

        /* Native methods have their parameters stored where the registers
         * normally are stored. */
        int i, j;
        const u4* framePtr = (const u4*)fp;
        for(i = j = 0; i < method->registersSize; i++, j++) {
          u4 rval = *framePtr++;
          if(isParamObject(method, j)) {
            Object* obj = (Object*)rval;
            if(obj) offAddObjectIntoTrack(obj, NULL, fb);
            rval = auxObjectToId(obj);
          } else if(isParamLong(method, j)) {
            writeU4(sfb, rval);
            rval = *framePtr++; i++;
          }
          writeU4(sfb, rval);
        }
      }
    } else {
      /* Otherwise write out the method and pc first. */
      int addr = saveArea->xtra.currentPc - method->insns;
      writeU4(sfb, method->clazz->pDvmDex->id << 24 |
                  PACK_METHOD_IDX(method));
      writeU4(sfb, addr);

      /* Then transmit the stack information. */
      const RegisterMap* pMap = dvmGetExpandedRegisterMap(method);
      const u1* regVector = pMap ? dvmRegisterMapGetLine(pMap, addr) : NULL;
      if(regVector == NULL) {
        ALOGE("MISSING REGMAPS %s %s", method->clazz->descriptor, method->name);
      }
      assert(method->clazz->status >= CLASS_INITIALIZING);
      assert(regVector && "No register maps found");

//ALOGI("SENDING %s %s %d", method->clazz->descriptor, method->name, addr);

      int i;
      u2 bits = 1 << 1;
      const u4* framePtr = (const u4*)fp;
      for(i = 0; i < method->registersSize; i++) {
        u4 rval = *framePtr++;

        bits >>= 1;
        if(bits == 1) {
          bits = *regVector++ | 0x100;
        }

        if(bits & 0x01) {
          /* Register is a non-null object. */
          Object* obj = (Object*)rval;
          if(obj) offAddObjectIntoTrack(obj, NULL, fb);
          rval = auxObjectToId(obj);
        }

        writeU4(sfb, rval);
      }
      dvmReleaseRegisterMapLine(pMap, regVector);
    }
    fp = saveArea->prevFrame;
  }
  // write the count of break frames to server
  if(sst->curFrame != NULL) {
    for(u4 i = breakIncluded; i < thread->breakFrames; i++) {
      writeU4(sfb, 0);
    }
  }
  writeU4(sfb, (u4)-1);
}

void offPushStackServer(FifoBuffer* sfb, Thread* thread) {
  InterpSaveState* sst = &thread->interpSave;
  writeU4(sfb, thread->threadId);
  writeU1(sfb, thread->interrupted);

  if(thread->threadObj) offAddTrackedObject(thread->threadObj);
  if(thread->exception) offAddTrackedObject(thread->exception);
  writeU4(sfb, auxObjectToId(thread->threadObj));
  writeU4(sfb, auxObjectToId(thread->exception));
  offTransmitMonitors(thread, sfb);

  if(!gDvm.isServer && thread->offLocalOnly) {
    writeU4(sfb, 0);
    writeU4(sfb, 0);
    writeU4(sfb, (u4)-1);
    return;
  }
    
/*
#ifdef SYNC_STACK_ONLY
  assert(0 && "not supported yet");
  void* fp = gDvm.isServer || thread == dvmThreadSelf() ?
        thread->curFrame : NULL;
#else
*/
  u4* fp = sst->curFrame;
  u4 stackOffset;
  if(fp == NULL) {
    stackOffset = 0U;
  } else {
    stackOffset = (u1*)thread->offStackFpStop - (u1*)fp; //TODO: might be wrong, see if we need to add or subtract another sizeof(StackSaveArea)
  }
  writeU4(sfb, stackOffset); // stack offset
  writeU4(sfb, thread->breakFrames); // thread->breakFrames

  while(fp != thread->offStackFpStop) {
    const StackSaveArea* saveArea = SAVEAREA_FROM_FP(fp);
    Method* method = (Method*)saveArea->method;

    if(dvmIsBreakFrame(fp)) {
      /* Just write the invalid method id to indicate break frame. */
      writeU4(sfb, 0);
    } else if(dvmIsNativeMethod(method)) {
      writeU4(sfb, method->clazz->pDvmDex->id << 24 |
                  PACK_METHOD_IDX(method));
      writeU8(sfb, (u8)(uintptr_t)saveArea->xtra.localRefCookie);

      if(saveArea->prevFrame &&
         SAVEAREA_FROM_FP(saveArea->prevFrame)->method == method) {
        writeU1(sfb, 0);
      } else {
        writeU1(sfb, 1);

        /* Native methods have their parameters stored where the registers
         * normally are stored. */
        int i, j;
        const u4* framePtr = (const u4*)fp;
        for(i = j = 0; i < method->registersSize; i++, j++) {
          u4 rval = *framePtr++;
          if(isParamObject(method, j)) {
            Object* obj = (Object*)rval;
            if(obj) offAddTrackedObject(obj);
            rval = auxObjectToId(obj);
          } else if(isParamLong(method, j)) {
            writeU4(sfb, rval);
            rval = *framePtr++; i++;
          }
          writeU4(sfb, rval);
        }
      }
    } else {
      /* Otherwise write out the method and pc first. */
      int addr = saveArea->xtra.currentPc - method->insns;
      writeU4(sfb, method->clazz->pDvmDex->id << 24 |
                  PACK_METHOD_IDX(method));
      writeU4(sfb, addr);

      /* Then transmit the stack information. */
      const RegisterMap* pMap = dvmGetExpandedRegisterMap(method);
      const u1* regVector = pMap ? dvmRegisterMapGetLine(pMap, addr) : NULL;
      if(regVector == NULL) {
        ALOGE("MISSING REGMAPS %s %s", method->clazz->descriptor, method->name);
      }
      assert(method->clazz->status >= CLASS_INITIALIZING);
      //assert(regVector && "No register maps found");

//ALOGI("SENDING %s %s %d", method->clazz->descriptor, method->name, addr);

      int i;
      u2 bits = 1 << 1;
      const u4* framePtr = (const u4*)fp;
      if(thread->returnType == 'e') {
          ALOGE("write register num: %d", method->registersSize);
          for(i = 0; i < method->registersSize - method->insSize; i++) {
              framePtr++;
              ALOGE("write register null");
              writeU4(sfb, COMM_INVALID_ID);
          }
          DexParameterIterator iterator;
          const char* descriptor;
          dexParameterIteratorInit(&iterator, &method->prototype);
          for(i = 0; i < method->insSize; i++) {
              bool isRef = false;
              u4 rval = *framePtr++;
              if(i == 0 && !dvmIsStaticMethod(method)) {
                  isRef = true;
              }
              if(i > 0 || dvmIsStaticMethod(method)) {
                  descriptor = dexParameterIteratorNextDescriptor(&iterator);
                  //if(descriptor == NULL) {
                  //    break;
                  //}
                  // we only cares object parameter
                  if(*descriptor == 'L' || *descriptor == '[') {
                      isRef = true;
                  }
              }
              if(isRef) {
                  Object* obj = (Object*)rval;
                  if(obj) offAddTrackedObject(obj);
                  rval = auxObjectToId(obj);
                  ALOGE("write register object");
              } else {
                  ALOGE("write register nonobject");
              }
              writeU4(sfb, rval);
          }
      } else if(thread->returnType == 'v' || thread->returnType == 'w' || thread->returnType == 'i' || thread->returnType == 'o') {
        //ALOGE("the return type is: %d, the return reg is: %d, regVec is: %d", thread->returnType, thread->retReg, *regVector);
        for(i = 0; i < method->registersSize; i++) {
          u4 rval = *framePtr++;

          bits >>= 1;
          if(bits == 1) {
            bits = *regVector++ | 0x100;
          }

          if(thread->returnType == 'v' || thread->returnType == 'e' || !(thread->retReg == i || (thread->returnType == 'w' && (thread->retReg + 1) == i))) {
            writeU4(sfb, COMM_INVALID_ID);
          } else {
            //ALOGE("get a return obj at reg: %d", i);
            if(bits & 0x01) {
              // Register is a non-null object.
              Object* obj = (Object*)rval;
              if(obj) offAddTrackedObject(obj);
              rval = auxObjectToId(obj);
            }
            //ALOGE("the rvalue we get is: %d", rval);
            writeU4(sfb, rval);
          }
        }
      } else {
        //ALOGE("regVec is: %d", *regVector);
        for(i = 0; i < method->registersSize; i++) {
          u4 rval = *framePtr++;

          bits >>= 1;
          if(bits == 1) {
            bits = *regVector++ | 0x100;
          }

          if(bits & 0x01) {
            /* Register is a non-null object. */
            //ALOGE("the reg %d is an object", i);
            Object* obj = (Object*)rval;
            if(obj) offAddTrackedObject(obj);
            rval = auxObjectToId(obj);
          }
 
          //ALOGE("the rvalue we get for %i is: %d", i, rval);
          writeU4(sfb, rval);
        }
      }
      dvmReleaseRegisterMapLine(pMap, regVector);
    }
    fp = saveArea->prevFrame;
  }
  writeU4(sfb, (u4)-1);
}

void offPushStack(FifoBuffer* sfb, FifoBuffer* fb, Thread* thread) {
    // Modified by Yong, differentiate the server and local cases
    if(gDvm.isServer) {
        offPushStackServer(sfb, thread);
        thread->returnType = ' ';
    } else {
        if(thread->isMethodStart) {
          thread->isMethodStart = false;
          offPushStackLocalMethodStart(sfb, fb, thread);
          //ALOGE("offload at the start of method");
        } else {
          offPushStackLocalInMethod(sfb, fb, thread);
          //ALOGE("offload at the middle of method");
        }
    }
}

Thread* offPullStackServer(FifoBuffer* sfb, u4 tid) {
  Thread* thread = offIdToThread(tid);
  InterpSaveState* sst = &thread->interpSave;
  u4* fp;
  u1* stackPtr,* basePtr;

  u4 mid;
  FifoBuffer stack = auxFifoCreate();
  Queue frameQueue = auxQueueCreate();

  thread->interrupted = (bool)readU1(sfb);
  thread->threadObj = offIdToObject(readU4(sfb));
  thread->exception = offIdToObject(readU4(sfb));
  offReceiveMonitors(thread, sfb);

  u4 stackOffset = readU4(sfb);
  thread->breakFrames = readU4(sfb);
  for(mid = readU4(sfb); mid != (u4)-1; mid = readU4(sfb)) {
    StackSaveArea saveArea;
    memset(&saveArea, 0, sizeof(saveArea));
    auxQueuePushI(&frameQueue, auxFifoSize(&stack) + sizeof(saveArea));

    if(mid == 0) {
      /* Break frame */
      auxFifoPushData(&stack, (char*)&saveArea, sizeof(saveArea));
    } else {
      Method* method = auxMethodByIdx(offIdToDex(mid >> 24),
                                    GET_METHOD_IDX(mid), GET_METHOD_STATIC(mid),
                                    GET_METHOD_DIRECT(mid), false);
      assert(method->clazz->status == CLASS_INITIALIZED ||
             method->clazz->status == CLASS_INITIALIZING);

      if(dvmIsNativeMethod(method)) {
        /* Although this value may be a pointer it's OK to send back and forth
         * as only the endpoint that's actually responsible for the native frame
         * will read this value. */
        saveArea.xtra.localRefCookie =
            (typeof(saveArea.xtra.localRefCookie))(uintptr_t)readU8(sfb);
        saveArea.method = method;
        auxFifoPushData(&stack, (char*)&saveArea, sizeof(saveArea));

        u1 hasParams = readU1(sfb);
        if(hasParams) {
          int i, j;
          for(i = j = 0; i < method->registersSize; i++, j++) {
            u4 rval = readU4(sfb);
            if(isParamObject(method, j)) {
              rval = (u4)offIdToObject(rval);
            } else if(isParamLong(method, j)) {
              auxFifoPushData(&stack, (char*)&rval, sizeof(rval));
              rval = readU4(sfb); i++;
            }
            auxFifoPushData(&stack, (char*)&rval, sizeof(rval));
          }
        }
        continue;
      }

      int addr = readU4(sfb);
      saveArea.xtra.currentPc = method->insns + addr;
      saveArea.method = method;
      auxFifoPushData(&stack, (char*)&saveArea, sizeof(saveArea));

      const RegisterMap* pMap = dvmGetExpandedRegisterMap(method);
      const u1* regVector = pMap ? dvmRegisterMapGetLine(pMap, addr) : NULL;
      if(regVector == NULL) {
        ALOGE("MISSING REGMAPS %s %s addr: %d", method->clazz->descriptor, method->name, addr);
      }
      assert(regVector && "No register maps found");

      if (addr != 0) {
          int i;
          u2 bits = 1 << 1;
          for(i = 0; i < method->registersSize; i++) {
            u4 rval = readU4(sfb);

            bits >>= 1;
            if(bits == 1) {
              bits = *regVector++ | 0x100;
            }

            if(bits & 0x01) {
              /* Register is a non-null object. */
              rval = (u4)offIdToObject(rval);
            }

            auxFifoPushData(&stack, (char*)&rval, sizeof(rval));
          }
      } else {
          int i;
          int argStart = method->registersSize - method->insSize;
          //ALOGE("value of i is: %d, regsize is: %d", i, method->registersSize);
          u2 bits = 1 << 1;
          //regVector += i / 8;
          //bits = (*regVector++ | 0x100) >> (i % 8);
          //bits <<= 1;
          for(i = 0; i < method->registersSize; i++) {
            u4 rval = readU4(sfb);

            bits >>= 1;
            if(bits == 1) {
              bits = *regVector++ | 0x100;
            }

            if(i >= argStart && (bits & 0x01)) {
              /* Register is a non-null object. */
             // ALOGE("offloading receive: id: %d", rval);
              rval = (u4)offIdToObject(rval);
              //ALOGE("get object with the address of: %u", rval);
            }

            auxFifoPushData(&stack, (char*)&rval, sizeof(rval));
          }
      }
      dvmReleaseRegisterMapLine(pMap, regVector);
    }
  }

  if(auxFifoSize(&stack) != stackOffset) {
    ALOGE("FAIL %d %d", auxFifoSize(&stack), stackOffset);
  }
  assert(auxFifoSize(&stack) == stackOffset);

  /* Copy in the stack now that we've built it. */
  if(stackOffset == 0 && auxQueueEmpty(&frameQueue)) {
    sst->curFrame = NULL;
    goto noframes;
  }

  assert(!auxQueueEmpty(&frameQueue));
  assert(auxFifoSize(&stack) <= (u4)thread->interpStackSize);
  assert(auxFifoSize(&stack) <= stackOffset);
  stackPtr = thread->interpStackStart - stackOffset;
  basePtr = stackPtr;
  assert(thread->interpStackEnd <= basePtr);
  sst->curFrame = (u4*)(basePtr + auxQueuePop(&frameQueue).i);

  while(!auxFifoEmpty(&stack)) {
    u4 sz = auxFifoGetBufferSize(&stack);
    memcpy(stackPtr, auxFifoGetBuffer(&stack), sz);
    auxFifoPopBytes(&stack, sz);
    stackPtr += sz;
  }
  auxFifoDestroy(&stack);

  /* Fix up the prevFrame pointers. */
  fp = sst->curFrame;
  while(1) {
    StackSaveArea* saveArea = SAVEAREA_FROM_FP(fp);
//TODO: this is a problem
    if(auxQueueEmpty(&frameQueue)) {
      saveArea->prevFrame = NULL;
      StackSaveArea* stopSaveArea = SAVEAREA_FROM_FP(thread->offStackFpStop);
      thread->offStackFpStop = stopSaveArea->prevFrame;
      break;
    }
    if(!dvmIsBreakFrame(fp)) {
        thread->offStackFpStop = fp;
    }
    fp = saveArea->prevFrame = (u4*)(basePtr + auxQueuePop(&frameQueue).i);
    saveArea->savedPc = SAVEAREA_FROM_FP(fp)->xtra.currentPc;
    assert((u1*)saveArea->prevFrame <= thread->interpStackStart);
  }
  auxQueueDestroy(&frameQueue);

noframes:
  #ifdef DEBUG
  /* Do a quick debug check. */
  fp = sst->curFrame;
  u4 breaks = 0;
  while(fp) {
    StackSaveArea* saveArea = SAVEAREA_FROM_FP(fp);
    assert((uintptr_t)saveArea->prevFrame > (uintptr_t)fp ||
           saveArea->prevFrame == NULL);
    if(dvmIsBreakFrame(fp)) breaks++;
    fp = saveArea->prevFrame;
  }
  assert(breaks == thread->breakFrames);
  #endif

  return thread;
}

Thread* offPullStackLocal(FifoBuffer* sfb, u4 tid) {
  Thread* thread = offIdToThread(tid);
  InterpSaveState* sst = &thread->interpSave;
  u4* fp;
  u1* stackPtr,* basePtr;

  u4 mid;
  FifoBuffer stack = auxFifoCreate();
  Queue frameQueue = auxQueueCreate();

  thread->interrupted = (bool)readU1(sfb);
  thread->threadObj = offIdToObject(readU4(sfb));
  thread->exception = offIdToObject(readU4(sfb));
  offReceiveMonitors(thread, sfb);

  u4 stackOffset = readU4(sfb);
  thread->breakFrames = readU4(sfb);
  //ALOGE("break Frame is: %d", thread->breakFrames);
  for(mid = readU4(sfb); mid != (u4)-1; mid = readU4(sfb)) {
    StackSaveArea saveArea;
    memset(&saveArea, 0, sizeof(saveArea));
    auxQueuePushI(&frameQueue, auxFifoSize(&stack) + sizeof(saveArea));

    if(mid == 0) {
      /* Break frame */
      auxFifoPushData(&stack, (char*)&saveArea, sizeof(saveArea));
    } else {
      Method* method = auxMethodByIdx(offIdToDex(mid >> 24),
                                    GET_METHOD_IDX(mid), GET_METHOD_STATIC(mid),
                                    GET_METHOD_DIRECT(mid), false);
      assert(method->clazz->status == CLASS_INITIALIZED ||
             method->clazz->status == CLASS_INITIALIZING);

      if(dvmIsNativeMethod(method)) {
        /* Although this value may be a pointer it's OK to send back and forth
         * as only the endpoint that's actually responsible for the native frame
         * will read this value. */
        saveArea.xtra.localRefCookie =
            (typeof(saveArea.xtra.localRefCookie))(uintptr_t)readU8(sfb);
        saveArea.method = method;
        auxFifoPushData(&stack, (char*)&saveArea, sizeof(saveArea));

        u1 hasParams = readU1(sfb);
        if(hasParams) {
          int i, j;
          for(i = j = 0; i < method->registersSize; i++, j++) {
            u4 rval = readU4(sfb);
            if(isParamObject(method, j)) {
              rval = (u4)offIdToObject(rval);
            } else if(isParamLong(method, j)) {
              auxFifoPushData(&stack, (char*)&rval, sizeof(rval));
              rval = readU4(sfb); i++;
            }
            auxFifoPushData(&stack, (char*)&rval, sizeof(rval));
          }
        }
        continue;
      }

      int addr = readU4(sfb);
      saveArea.xtra.currentPc = method->insns + addr;
      saveArea.method = method;
      auxFifoPushData(&stack, (char*)&saveArea, sizeof(saveArea));

      const RegisterMap* pMap = dvmGetExpandedRegisterMap(method);
      const u1* regVector = pMap ? dvmRegisterMapGetLine(pMap, addr) : NULL;
      if(regVector == NULL) {
        ALOGE("MISSING REGMAPS %s %s addr: %d", method->clazz->descriptor, method->name, addr);
      }
      //assert(regVector && "No register maps found");

      if(thread->exception) {
          int i;
          for(i = 0; i < method->registersSize - method->insSize; i++) {
              u4 rval = readU4(sfb);
              auxFifoPushData(&stack, (char*)&rval, sizeof(rval));
          }
          DexParameterIterator iterator;
          const char* descriptor;
          dexParameterIteratorInit(&iterator, &method->prototype);
          for(i = 0; i < method->insSize; i++) {
              u4 rval = readU4(sfb);
              bool isRef = false;
              if(i == 0 && !dvmIsStaticMethod(method)) {
                  isRef = true;
              }
              if(i > 0 || dvmIsStaticMethod(method)) {
                  descriptor = dexParameterIteratorNextDescriptor(&iterator);
                  //if(descriptor == NULL) {
                  //    break;
                  //}
                  // we only cares object parameter
                  if(*descriptor == 'L' || *descriptor == '[') {
                      isRef = true;
                  }
              }
              if(isRef) {
                  rval = (u4)offIdToObject(rval);
              }
              auxFifoPushData(&stack, (char*)&rval, sizeof(rval));
          }
      } else if (addr != 0) {
          int i;
          u2 bits = 1 << 1;
          for(i = 0; i < method->registersSize; i++) {
            u4 rval = readU4(sfb);

            bits >>= 1;
            if(bits == 1) {
              bits = *regVector++ | 0x100;
            }

            if(bits & 0x01) {
              /* Register is a non-null object. */
              rval = (u4)offIdToObject(rval);
            }
            auxFifoPushData(&stack, (char*)&rval, sizeof(rval));
          }
      } else {
          ALOGE("enter in start or with exception");
          int i;
          int argStart = method->registersSize - method->insSize;
          //ALOGE("value of i is: %d, regsize is: %d", i, method->registersSize);
          u2 bits = 1 << 1;
          //regVector += i / 8;
          //bits = (*regVector++ | 0x100) >> (i % 8);
          //bits <<= 1;
          for(i = 0; i < method->registersSize; i++) {
            u4 rval = readU4(sfb);

            bits >>= 1;
            if(bits == 1) {
              bits = *regVector++ | 0x100;
            }

            if(i >= argStart && (bits & 0x01)) {
              /* Register is a non-null object. */
              //ALOGE("offloading receive: id: %d", rval);
              rval = (u4)offIdToObject(rval);
              //ALOGE("get object with the address of: %u", rval);
            }

            auxFifoPushData(&stack, (char*)&rval, sizeof(rval));
          }
      }
      dvmReleaseRegisterMapLine(pMap, regVector);
    }
  }

  if(auxFifoSize(&stack) != stackOffset) {
    ALOGE("FAIL %d %d", auxFifoSize(&stack), stackOffset);
  }
  assert(auxFifoSize(&stack) == stackOffset);

  /* Copy in the stack now that we've built it. */
  if(stackOffset == 0 && auxQueueEmpty(&frameQueue)) {
    sst->curFrame = NULL;
    goto noframes;
  }

  assert(!auxQueueEmpty(&frameQueue));
  assert(auxFifoSize(&stack) <= (u4)thread->interpStackSize);
  assert(auxFifoSize(&stack) <= stackOffset);
  if(thread->offStackFpStop != NULL) {
    stackPtr = (u1*)thread->offStackFpStop - sizeof(StackSaveArea) - stackOffset;
  } else {
    stackPtr = thread->interpStackStart - stackOffset;
  }
  basePtr = stackPtr;
  assert(thread->interpStackEnd <= basePtr);
  sst->curFrame = (u4*)(basePtr + auxQueuePop(&frameQueue).i);

  while(!auxFifoEmpty(&stack)) {
    u4 sz = auxFifoGetBufferSize(&stack);
    memcpy(stackPtr, auxFifoGetBuffer(&stack), sz);
    auxFifoPopBytes(&stack, sz);
    stackPtr += sz;
  }
  auxFifoDestroy(&stack);

  /* Fix up the prevFrame pointers. */
  fp = sst->curFrame;
  while(1) {
    StackSaveArea* saveArea = SAVEAREA_FROM_FP(fp);
    fp = saveArea->prevFrame;
//TODO: this is a problem
    if(auxQueueEmpty(&frameQueue)) {
      saveArea->prevFrame = thread->offStackFpStop;
      if(saveArea->prevFrame != NULL) {
        saveArea->savedPc = SAVEAREA_FROM_FP(saveArea->prevFrame)->xtra.currentPc;
      }
      break;
    }
    fp = saveArea->prevFrame = (u4*)(basePtr + auxQueuePop(&frameQueue).i);
    saveArea->savedPc = SAVEAREA_FROM_FP(fp)->xtra.currentPc;
    assert((u1*)saveArea->prevFrame <= thread->interpStackStart);
  }
  auxQueueDestroy(&frameQueue);

noframes:
  #ifdef DEBUG
  /* Do a quick debug check. */
  fp = sst->curFrame;
  u4 breaks = 0;
  while(fp) {
    StackSaveArea* saveArea = SAVEAREA_FROM_FP(fp);
    assert((uintptr_t)saveArea->prevFrame > (uintptr_t)fp ||
           saveArea->prevFrame == NULL);
    if(dvmIsBreakFrame(fp)) breaks++;
    fp = saveArea->prevFrame;
  }
  //ALOGE("breaks is: %d, thread break frames: %d", breaks, thread->breakFrames);
  assert(breaks == thread->breakFrames);
  #endif

  return thread;
}

Thread* offPullStack(FifoBuffer* sfb, u4 tid) {
  Thread* thread;
  if(gDvm.isServer) {
    thread = offPullStackServer(sfb, tid);
  } else {
    thread = offPullStackLocal(sfb, tid);
  }

  return thread;
}

#ifdef DEBUG
bool offCheckBreakFrames() {
  u4 breaks = 0;
  Thread* self = dvmThreadSelf();
  InterpSaveState* sst = &self->interpSave;
  u4* fp = sst->curFrame;
  while(fp) {
    if(dvmIsBreakFrame(fp)) breaks++;
    fp = SAVEAREA_FROM_FP(fp)->prevFrame;
  }
  return breaks == self->breakFrames;
}

int offDebugStack(const Thread* thread) {
  const InterpSaveState* sst = &thread->interpSave;
  u4* fp = sst->curFrame;
  while(fp) {
    const StackSaveArea* saveArea = SAVEAREA_FROM_FP(fp);
    const Method* method = saveArea->method;
    if(dvmIsBreakFrame(fp)) {
      ALOGI("BREAK");
    } else {
      int addr = saveArea->xtra.currentPc - method->insns;
      ALOGI("%s %s %d\n", method->clazz->descriptor, method->name, addr);
    }
    fp = saveArea->prevFrame;
  }
  return thread->threadId;
}
#endif
