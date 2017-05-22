#include<assert.h>

// There is no inconsistencies in this code.  This is an example to
// show that we lower C assert's into assume's correctly.

typedef struct example_s {
    int natoms;
    char *mark;
} example;


int tst_bit(char *bv, int i) {
    int j;
    char mask;

    j = i >> 3;
    mask = 1 << (i & 0x7);
    return bv[j] & mask; // converted to bool
}


int rdl_atom_is_assigned(example *table, int i) {
    assert(0 <= i && i < table->natoms);
    return tst_bit(table->mark, i);
}
