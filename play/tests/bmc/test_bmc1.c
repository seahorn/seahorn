extern int __VERIFIER_NONDET();
int main(){
int x=0;
int y=0;

while (x < 100) {
if (__VERIFIER_NONDET()) y=1;
x = x + 4;
}

if (!(y >= 0 && y <= 1))
    goto ERR;
if (!(x <= 103))
    goto ERR;

SAFE: goto SAFE;
ERR: return 42;
}
