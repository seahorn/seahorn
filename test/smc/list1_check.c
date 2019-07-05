// RUN: %sea pf -O0 --inline "%s" 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include <seahorn/seahorn.h>
#include <stddef.h>
#include <stdint.h>

#include <stdio.h>
#include <stdlib.h>

#define FOO_TAG 100
#define BAR_TAG 200

static int8_t *g_bgn;
static int8_t *g_end;
static int g_active;

extern int nd(void);
extern int8_t *nd_ptr(void);

typedef struct Foo {
  int tag;
  int x;
} Foo;

typedef struct Bar {
  struct Foo foo;
  int y;
} Bar;

void *xmalloc(size_t sz) {
  void *p;
  p = malloc(sz);
  assume(((ptrdiff_t)p) > 0);
  return p;
}
Foo *mk_foo(int x) {
  Foo *res = (Foo *)xmalloc(sizeof(struct Foo));
  res->tag = FOO_TAG;
  res->x = x;

  if (!g_active && nd()) {
    g_active = !g_active;
    assume((int8_t *)res == g_bgn);
    assume(g_bgn + sizeof(struct Foo) == g_end);
  } else {
    assume((int8_t *)res > g_end);
  }

  return res;
}

Bar *mk_bar(int x, int y) {
  Bar *res = (Bar *)xmalloc(sizeof(struct Bar));
  res->foo.tag = BAR_TAG;
  res->foo.x = x;
  res->y = y;

  assume((int8_t *)res > g_end);
  return res;
}

Foo *to_foo(Bar *b) { return (Foo *)b; }
int is_bar(Foo *b) { return b->tag == BAR_TAG; }
int is_foo(Foo *b) { return b->tag == FOO_TAG; }
Bar *to_bar(Foo *b) { return (Bar *)b; }

typedef struct Entry {
  void *data;
  struct Entry *next;
} Entry;

typedef struct List {
  Entry *head;
} List;

Entry *mk_entry(void *data) {
  Entry *res = (Entry *)xmalloc(sizeof(struct Entry));
  res->data = data;
  res->next = NULL;
  assume((int8_t *)res > g_end);
  return res;
}

List *mk_list() {
  List *res = (List *)xmalloc(sizeof(struct List));
  res->head = NULL;

  assume((int8_t *)res > g_end);
  return res;
}

void insert(List *lst, void *data) {
  Entry *en = mk_entry(data);
  en->next = lst->head;
  lst->head = en;
}

int main(void) {
  List *lst;
  Entry *it;

  g_bgn = nd_ptr();
  g_end = nd_ptr();
  assume(g_bgn > 0);
  assume(g_end > g_bgn);

  g_active = 0;

  lst = mk_list();
  insert(lst, mk_foo(2));
  insert(lst, mk_bar(3, 4));
  insert(lst, mk_foo(5));

  unsigned cnt;
  cnt = 0;
  for (it = lst->head; it != NULL; it = it->next) {
    Foo *v = (Foo *)(it->data);
    if (is_bar(v)) {
      Bar *b;

      if (g_active) {
        sassert((int8_t *)v != g_bgn);
      }

      b = to_bar(v);
      printf("bar: x=%d, y=%d\n", v->x, b->y);
    } else {
      printf("foo: x=%d\n", v->x);
    }
    cnt++;
    if (cnt > 3)
      break;
  }
  return 0;
}
