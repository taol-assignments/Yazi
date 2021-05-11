  alloc_func zalloc;  /* used to allocate the internal state */
  free_func  zfree;   /* used to free the internal state */
  void     *opaque;   /* private data object passed to zalloc and zfree */
