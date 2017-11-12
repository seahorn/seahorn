#include "seahorn/seahorn.h"
#include <stdarg.h>
#include <cstdint>
#include <cstdio>
#undef NDEBUG
#include <cassert>
#include <cstdlib>
#include <cstring>
#include <map>
#include <functional>

extern "C" {

void sealog (const char *format, ...) {
    va_list args;
    va_start(args, format);
    if (std::getenv("SEAHORN_RT_VERBOSE"))
        vprintf(format, args);
    va_end(args);
}

void __VERIFIER_error() {
  printf("[sea] __VERIFIER_error was executed\n");
  exit(1);
}

void __VERIFIER_assume(int x) {
  assert(x);
}

#define get_value_helper(ctype, llvmtype)                               \
  ctype __seahorn_get_value_ ## llvmtype (int ctr, ctype *g_arr, int g_arr_sz) { \
    assert (ctr < g_arr_sz && "Unexpected index");                      \
    sealog("[sea] __seahorn_get_value_(" #llvmtype ", %d, %d)\n", ctr, g_arr_sz); \
    return g_arr[ctr];                                                  \
  }

#define get_value_int(bits) get_value_helper(int ## bits ## _t, i ## bits)

get_value_int(64)
get_value_int(32)
get_value_int(16)
get_value_int(8)

get_value_helper(intptr_t, ptr_internal)

const int MEM_REGION_SIZE_GUESS = 4000;
const int TYPE_GUESS = sizeof(int);

  std::map<intptr_t, intptr_t, std::greater<intptr_t>> absptrmap;

  /*intptr_t __seahorn_get_value_ptr(int ctr, intptr_t *g_arr, int g_arr_sz, int ebits) {
  static std::unordered_map<intptr_t, intptr_t> absptrmap;
  intptr_t absptr = __seahorn_get_value_ptr_internal(ctr, g_arr, g_arr_sz);

  auto concptrfind = absptrmap.find(absptr);
  intptr_t concptr;
  if (concptrfind == absptrmap.end()) {
    concptr = (intptr_t) calloc(MEM_REGION_SIZE_GUESS, ebits == 0 ? TYPE_GUESS : ebits);
    absptrmap.insert({absptr, concptr});
  } else {
    concptr = concptrfind->second;
  }

  printf("Returning %#lx for abstract pointer %#lx\n", concptr, absptr);

  return concptr;
  }*/

  intptr_t __seahorn_get_value_ptr(int ctr, intptr_t *g_arr, int g_arr_sz, int ebits) {
    intptr_t absptr = __seahorn_get_value_ptr_internal(ctr, g_arr, g_arr_sz);

    size_t sz = MEM_REGION_SIZE_GUESS * (ebits == 0 ? TYPE_GUESS : ebits);

    absptrmap[absptr] = absptr + sz;

    sealog("[sea] returning a pointer to an abstract region [%#lx, %#lx]\n", absptr, absptrmap.at(absptr));

    return absptr;
  }

  bool is_dummy_address (void *addr) {

    intptr_t ip = intptr_t (addr);
    auto it = absptrmap.lower_bound (ip+1);
    if (it == absptrmap.end()) return false;
    intptr_t lb = it->first;
    intptr_t ub = it->second;

    return (ip >= lb && ip < ub);
  }

  bool is_legal_address (void *addr) {
    return ! is_dummy_address (addr);
  }

/** Dummy implementation of memory wrapping functions */

void __seahorn_mem_store (void *src, void *dst, size_t sz)
{
  sealog("[sea] __seahorn_mem_store from %p to %p\n", src, dst);
  if (is_legal_address (dst)) {
  /* if dst is a legal address */
    sealog("[sea] memory write\n");
    memcpy (dst, src, sz);
  }
  /* else if dst is illegal, do nothing */
  else sealog("[sea] ignoring write to illegal memory address\n");
}

void __seahorn_mem_load (void *dst, void *src, size_t sz)
{
  sealog("__seahorn_mem_load from %p to %p\n", src, dst);
  if (is_legal_address (src)) {
  /* if src is a legal address */
    sealog("[sea] memory read\n");
    memcpy (dst, src, sz);
  }
  /* else, if src is illegal, return a dummy value */
  else { sealog("[sea] ignoring read from an illegal memory address\n"); bzero(dst, sz); }
}

// Dummy klee_make_symbolic function
void klee_make_symbolic(void *v, size_t sz, char *fname) {
  sealog("[sea] calling klee_make_symbolic for %s\n", fname);
}

void klee_assume(int b) {
  sealog("[sea] calling klee_assume\n");
  __VERIFIER_assume (b);
}

  void __assert_fail (const char * assertion, const char * file,
                      unsigned int line, const char * function) {
    printf("[sea] exiting with a call to __assert_fail\n");
    exit(1);
  }


}
