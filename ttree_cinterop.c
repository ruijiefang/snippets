/* ruijief: this is our custom cinterop.c file for the tournament tree
    that supports allocating heap memory.
    we also defined several helper functions for e.g. calculating pointer offsets and
    printing neatly. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* Malloc's a heap-allocated array of int64's and memset everything to 0. */
int64_t *ll_malloc(int64_t size) {
  int64_t *p = (int64_t *) malloc(size);
  memset(p, 0, size);
  /* printf("***ll_malloc: allocated %lld bytes and set to zero at %p\n", size, p); */
  return p;
}

/* Frees a heap-allocated array of int64's */
int64_t ll_free(int64_t *p) {
  free((void *)p);
  return 0;
}

/* String-to-int64 function */
int64_t ll_atoi64(int8_t *ls) {
  char *s = (char*)ls;
  return (int64_t)atoi(s);
}

/* Calculates two void pointer differences and return an int64_t */
int64_t ll_pointer_sub(int8_t *p1, int8_t *p2) {
  return (int64_t)(((void*)p1) - ((void*)p2));
}

/* Calculates the array index of an int64 array allocated on the heap */
int64_t* ll_int64_array_idx(int64_t* baseptr, int64_t offset) {
  /* printf("***ll_int64_array_idx: baseptr %p, offset %lld, content %lld\n", baseptr, offset, *(baseptr + offset)); */
  return baseptr + offset;
}

/* Helpful debugging functions */
/* Prints an int64 to stdout */
int64_t ll_print_int64(int64_t i) {
  printf("ll: %lld\n", i);
  return 0;
}

/* Prints a seperator string to stdout */
int64_t ll_print_seperator(int64_t _useless) {
  printf("------------------------------------------\n");
  return 0;
}
