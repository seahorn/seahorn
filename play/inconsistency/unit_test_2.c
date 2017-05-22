#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

// There is no inconsistencies in this code with --boa or --null

extern void __VERIFIER_error (void);
#define assert(c) if (!c) __VERIFIER_error ();

typedef struct {
  int* data;
  int size;
} my_vector;

void init_vector(my_vector* v, int size) {
  int i;
  v->data = (int*) malloc(size*sizeof(int));
  v->size = size;
  for (i = 0; i < size; ++ i) {
    v->data[i] = i;
  }
}

bool normalized_vector(const my_vector* v) {
  int i;
  for (i = 1; i < v->size; ++ i) {
    if (v->data[i-1] >= v->data[i]) {
      return false;
    }
  }
  return true;
}

int find_in_vector(const my_vector* v, int x) {
  int* a;
  int l, h, k;

  assert(normalized_vector(v) && v->size > 0);

  l = 0;
  h = v->size;
  a = v->data;
  for (;;) {
    k = (l + h) >> 1;
    assert(l <= k && k < h && h <= v->size);
    if (k == l) break;
    if (a[k] > x) {
      h = k;
    } else {
      l = k;
    }
  }

  if (a[k] == x) {
   return k;
  } else {
    return -1;
  }
}

int main() {
  int i;
  my_vector v;

  init_vector(&v, 100);
  i = find_in_vector(&v, 10);
  printf("i = %d\n", i);
  return 42;
}
