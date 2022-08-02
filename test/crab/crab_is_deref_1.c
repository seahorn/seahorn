// RUN: %sea -O3 fpf --inline --horn-bv2-crab-lower-is-deref --horn-bmc-crab-dom=zones --dsa=sea-cs-t --bmc=opsem --horn-vcgen-use-ite --horn-vcgen-only-dataflow=false --horn-bmc-coi=false --horn-stats=true --sea-opsem-allocator=static "%s" 2>&1 | OutputCheck %s
// RUN: %sea -O3 fpf --inline --horn-bv2-crab-check-is-deref --horn-bmc-crab-dom=zones --dsa=sea-cs-t --bmc=opsem --horn-vcgen-use-ite --horn-vcgen-only-dataflow=false --horn-bmc-coi=false --horn-stats=true --sea-opsem-allocator=static "%s" 2>&1 | OutputCheck %s
// CHECK: ^sat$
// CHECK: crab.isderef.solve 2

// With pk we can prove the three checks
#include <seahorn/seahorn.h>
#include <stdio.h>
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>

extern int nd_int(void);

size_t size_t_nd(void) {
    int res = nd_int();
    assume(res > 0);
    return res;
}

extern void memhavoc(void *, size_t);

struct aws_byte_cursor {
    /* do not reorder this, this struct lines up nicely with windows buffer structures--saving us allocations */
    size_t len;
    uint8_t *ptr;
};

struct aws_byte_buf {
    /* do not reorder this, this struct lines up nicely with windows buffer structures--saving us allocations.*/
    size_t len;
    uint8_t *buffer;
    size_t capacity;
    struct aws_allocator *allocator;
};

extern void *ext_memcpy (void *dest, const void *src, size_t len);

void *mymemcpy(void *dst, const void *src, size_t len) {
    sassert(sea_is_dereferenceable(dst, len));
    sassert(sea_is_dereferenceable(src, len));
    return ext_memcpy(dst, src, len);
}

void initialize_byte_buf(struct aws_byte_buf *const buf) {
    size_t len = size_t_nd();
    size_t cap = size_t_nd();
    assume(len <= cap);
    assume(cap <= 512);

    buf->len = len;
    buf->capacity = cap;
    buf->buffer = malloc(cap * sizeof(*(buf->buffer)));
}

void init_cursor_from_buf(struct aws_byte_buf *const buf, struct aws_byte_cursor *cur) {
    cur->len = buf->len;
    cur->ptr = malloc(sizeof(uint8_t) * cur->len);
}

int main(void) {
    struct aws_byte_buf buf;
    initialize_byte_buf(&buf);
    if (buf.capacity == 0) return 0;
    struct aws_byte_cursor cur;
    init_cursor_from_buf(&buf, &cur);

    sassert(sea_is_dereferenceable(buf.buffer, buf.len));
    if (buf.capacity - buf.len < cur.len) return -1;
    if (cur.len > 0)
        mymemcpy(buf.buffer + buf.len, cur.ptr, cur.len);
    return 0;
}

