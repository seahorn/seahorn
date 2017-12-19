// RUN: %sea smc -O0 "%s" 2>&1 | OutputCheck %s
// CHECK: ^sat$

#include<stdlib.h>
#include<stdio.h>

#define FOO_TAG 1
#define BAR_TAG 2

typedef struct Foo {
    int tag;
    int x;
} Foo;

typedef struct Bar {
    struct Foo foo;
    int y;
} Bar;

Foo *mk_foo (int x) {
    Foo *res = (Foo*) malloc(sizeof(struct Foo));
    res->tag = FOO_TAG;
    res->x = x;
    return res;
}

Bar *mk_bar (int x, int y) {
    Bar *res = (Bar*) malloc(sizeof(struct Bar));
    res->foo.tag = BAR_TAG;
    res->foo.x = x;
    res->y = y;
    return res;
}

Foo *to_foo(Bar *b) {return (Foo*)b;}
int is_bar (Foo *b) {return b->tag == BAR_TAG;}
Bar *to_bar (Foo *b) {return (Bar*)b;}



typedef struct Entry {
    void *data;
    struct Entry *next;
} Entry;

typedef struct List {
    Entry *head;
} List;

Entry *mk_entry (void *data) {
    Entry* res = (Entry*)malloc(sizeof(struct Entry));
    res->data = data;
    res->next = NULL;
    return res;
}

List *mk_list() {
    List *res = (List*) malloc(sizeof(struct List));
    res->head = NULL;
    return res;
}

void insert(List *lst, void *data) {
    Entry *en = mk_entry (data);
    en->next = lst->head;
    lst->head = en;
}

int main(void) {
    List *lst;
    Entry *it;

    lst = mk_list();
    insert (lst, mk_foo(2));
    insert (lst, mk_bar(3, 4));
    insert (lst, mk_foo(2));


    for (it = lst->head; it != NULL; it = it->next) {
        Foo *v = (Foo*)(it->data);
        if (is_bar(v)) {
            Bar *b;
            b = to_bar(v);
            printf ("bar: x=%d, y=%d\n", v->x, b->y);
        }
        else {
            printf("foo: x=%d\n", v->x);
        }
    }
    return 0;

}
