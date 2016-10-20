#include "Dalvik.h"

#define BASE_PROCESSING_DELAY 5000 // 5ms

INLINE u8 schedulerGetTime() {
  return dvmGetRelativeTimeUsec();
}

/*INLINE void offSchedulerSafePoint(Thread* self, const Method* method) {
  if(gDvm.offDisabled) return;
  //if(++self->offTimeCounter & 0x3FF) return;
  if(!method->clazz->pDvmDex->classLoader) return;
  if(!gDvm.isServer && self->offProtection == 0 && !self->offFlagMigration &&
     offWellConnected()) {
     // space bubble
     if(!strcmp(method->clazz->descriptor, "Lcom/google/ads/util/AdUtil;") && !strcmp(method->name, "a") && method->idx == 1156) {
        self->offFlagMigration = true;
     } else if(!strcmp(method->clazz->descriptor, "Lcom/pconline/spacebubbles/CLGameEngine;") && !strcmp(method->name, "ObterStringTabela") && method->idx == 2431) {
        self->offFlagMigration = true;
     } else if(!strcmp(method->clazz->descriptor, "Lcom/pconline/spacebubbles/CLGameEngine;") && !strcmp(method->name, "IniciarDadosJogo") && method->idx == 2406) {
        self->offFlagMigration = true;
     } else if(!strcmp(method->clazz->descriptor, "Lcom/mopub/mobileads/AdView;") && !strcmp(method->name, "configureAdViewUsingHeadersFromHttpResponse") && method->idx == 2408) {
        self->offFlagMigration = true;
     } else if(!strcmp(method->clazz->descriptor, "Lcom/google/ads/util/AdUtil;") && !strcmp(method->name, "b") && method->idx == 1165) {
        self->offFlagMigration = true;
     } else if(!strcmp(method->clazz->descriptor, "Lb;") && !strcmp(method->name, "a") && method->idx == 771) {
        self->offFlagMigration = true;
     } else if(!strcmp(method->clazz->descriptor, "Lcom/google/ads/util/AdUtil;") && !strcmp(method->name, "a") && method->idx == 1159) {
        self->offFlagMigration = true;
     } 
     // sudoku
     if(!strcmp(method->clazz->descriptor, "Lcom/genina/ads/AdView$MyLocalThread;") && !strcmp(method->name, "run") && method->idx == 1289) {
        self->offFlagMigration = true;
     } else if(!strcmp(method->clazz->descriptor, "Lcom/icenta/sudoku/ui/MobileSudoku$42;") && !strcmp(method->name, "run") && method->idx == 2996) {
        self->offFlagMigration = true;
     } else if(!strcmp(method->clazz->descriptor, "Lcom/icenta/sudoku/Puzzle;") && !strcmp(method->name, "solve") && method->idx == 2811) {
        self->offFlagMigration = true;
     } else if(!strcmp(method->clazz->descriptor, "Lcom/icenta/sudoku/Puzzle;") && !strcmp(method->name, "<init>") && method->idx == 2784) {
        self->offFlagMigration = true;
     } else if(!strcmp(method->clazz->descriptor, "Lcom/icenta/sudoku/ui/MobileSudoku;") && !strcmp(method->name, "saveLastPuzzle") && method->idx == 3267) {
        self->offFlagMigration = true;
     } else if(!strcmp(method->clazz->descriptor, "Lcom/icenta/sudoku/ui/MobileSudoku;") && !strcmp(method->name, "gotoMain") && method->idx == 3202) {
        self->offFlagMigration = true;
     } else if(!strcmp(method->clazz->descriptor, "Lcom/icenta/sudoku/Block;") && !strcmp(method->name, "processMultipleCanNotBeHereSoItsThere") && method->idx == 2683) {
        self->offFlagMigration = true;
     } else if(!strcmp(method->clazz->descriptor, "Lcom/icenta/sudoku/util/Hint;") && !strcmp(method->name, "restoreState") && method->idx == 3446) {
        self->offFlagMigration = true;
     }*/
    /*u8 threshold;
    if(gDvm.offSyncTimeSamples > 10) {
      threshold = 1 * gDvm.offSyncTime;
    } else {
      threshold = 1 * gDvm.offSyncTime * gDvm.offSyncTimeSamples +
          1 * (gDvm.offNetRTT + gDvm.offNetRTTVar) *
              (10 - gDvm.offSyncTimeSamples);
      threshold /= 10;
      threshold *= 1;
    }
    if(gDvm.methodExeTimeMap->find(method) != gDvm.methodExeTimeMap->end()) {
        //ALOGI("the offloading decision WITH METHOD %s.%s: threshold: %llu, (*gDvm.methodExeTimeMap)[method]: %llu", method->clazz->descriptor, method->name, threshold, (*gDvm.methodExeTimeMap)[method]); 
        self->offFlagMigration = threshold < (*gDvm.methodExeTimeMap)[method];
    }
    if(self->offFlagMigration) {
      ALOGI("FLAGGING %d WITH METHOD %s.%s FOR MIGRATE WITH %d %lld",
            self->threadId, method->clazz->descriptor, method->name, (*gDvm.methodExeTimeMap)[method], threshold);
    }*/
//  }
//}

/*INLINE void offSchedulerUnsafePoint(Thread* self) {
  if(gDvm.offDisabled) return;
  self->offFlagMigration = false;
  self->offUnsafeTime = schedulerGetTime();
  self->offTimeCounter = 0;
}*/

/* This function doesn't really belong here... */
/*INLINE void offStackFramePopped(Thread* self) {
  InterpSaveState* sst = &self->interpSave;
  if(sst->curFrame == NULL || self->offSyncStackStop == NULL) {
    self->offSyncStackStop = NULL;
  } else {
    void* nfp = SAVEAREA_FROM_FP(sst->curFrame)->prevFrame;
    if(nfp == NULL) {
      self->offSyncStackStop = NULL;
    } else {
      self->offSyncStackStop = nfp > self->offSyncStackStop ?
          nfp : self->offSyncStackStop;
    }
  }
}*/

