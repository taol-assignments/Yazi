#ifndef __Yazi_Allocator_H
#define __Yazi_Allocator_H

#define KRML_HOST_MALLOC(size) (strm->zalloc(strm->opaque, 1, size))
#define KRML_HOST_FREE(address) (strm->zfree(strm->opaque, address))

typedef void *(*alloc_func) (void *opaque, unsigned int items, unsigned int size);
typedef void (*free_func)  (void *opaque, void *address);

#endif
