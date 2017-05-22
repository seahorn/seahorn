extern void do_something(int * p);

void example4(int n) {
    int arr[n];
    int i;
    for (i=0; i<=n; i++) {
        arr[i]=i; // inconsistent off by one
    }
    do_something(&arr[0]);
}
