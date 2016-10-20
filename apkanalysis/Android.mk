
LOCAL_PATH:= $(call my-dir)

local_src_files := \
		AnalyzeMain.cpp

local_c_includes := \
		dalvik \
		dalvik/libdex \
		dalvik/vm \
		$(JNI_H_INCLUDE)
		
local_shared_libraries := \
		libssl \
		libdvm \
		libcrypto \
		libicuuc \
		libicui18n

include $(CLEAR_VARS)
ifeq ($(TARGET_CPU_SMP),true)
    LOCAL_CFLAGS += -DWITH_OFFLOAD \
                    -DANDROID_SMP=1
else
    LOCAL_CFLAGS += -DWITH_OFFLOAD \
                    -DANDROID_SMP=0
endif

LOCAL_SRC_FILES := $(local_src_files)
LOCAL_C_INCLUDES := $(local_c_includes)
LOCAL_SHARED_LIBRARIES := $(local_shared_libraries) libcutils libexpat liblog libz
LOCAL_MODULE_TAGS := optional
LOCAL_MODULE := apkanalysis

LOCAL_C_INCLUDES += bionic/ bionic/libstdc++/include external/stlport/stlport
LOCAL_SHARED_LIBRARIES += libstlport

include $(BUILD_EXECUTABLE)

ifeq ($(WITH_HOST_DALVIK),true)
    include $(CLEAR_VARS)
    LOCAL_SRC_FILES := $(local_src_files)
    LOCAL_C_INCLUDES := $(local_c_includes)
    LOCAL_SHARED_LIBRARIES := $(local_shared_libraries)
    LOCAL_STATIC_LIBRARIES :=  libcutils libexpat liblog libz
    LOCAL_LDLIBS += -ldl -lpthread
    LOCAL_CFLAGS += -DWITH_OFFLOAD \
                    -DANDROID_SMP=1
    LOCAL_MODULE_TAGS := optional
    LOCAL_MODULE := apkanalysis
    include $(BUILD_HOST_EXECUTABLE)
endif
