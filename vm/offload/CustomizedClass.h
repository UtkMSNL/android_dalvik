
/*
 * Load the named class (by descriptor) from the specified DEX file.
 * Used by class loaders to instantiate a class object from a
 * VM-managed DEX.
 */
ClassObject* customDefineClass(DvmDex* pDvmDex, const char* descriptor,
    Object* classLoader);
    
ClassObject* customFindClassNoInit(const char* descriptor,
        Object* loader);
