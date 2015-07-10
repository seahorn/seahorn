extern int nd ();

extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
void assert (int v) { if (!v) __VERIFIER_error (); }

#define assume __VERIFIER_assume

int main() {
    int k=0;
    int x = nd ();
    assume (x>0);
    for (int i=-x; i<x; i++) {
        if (i == 0) goto LOOP;
        k=1/1;
    }
    return k;
 LOOP: goto LOOP;
}
