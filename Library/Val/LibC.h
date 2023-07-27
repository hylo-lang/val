#include <stdio.h>
#include <malloc.h>

#ifdef _WIN32 
void* aligned_alloc(size_t alignment, size_t size) {
    return _aligned_malloc(size, alignment);
}

void free(void* memblock) {
    _aligned_free(memblock);
}

FILE* fdopen(int fd, const char* mode) {
    return _fdopen(fd, mode);
}
#else

#endif