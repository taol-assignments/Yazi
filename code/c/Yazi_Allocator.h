#ifndef __Yazi_Allocator_H
#define __Yazi_Allocator_H

#define KRML_HOST_MALLOC(size) (strm->zalloc(strm->opaque, 1, size))
#define KRML_HOST_FREE(address) (strm->zfree(strm->opaque, address))

#endif
