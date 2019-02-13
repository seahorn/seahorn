// RUN: %sea bpf -O3 -m64 --inline --step=large --track=ptr --horn-bv-global-constraints=true  \
// RUN:           --enable-nondet-init --strip-extern --externalize-addr-taken-functions \
// RUN:           --horn-bv-singleton-aliases=true --devirt-functions --horn-bv-ignore-calloc=false \
// RUN:           --enable-indvar --enable-loop-idiom  --symbolize-constant-loop-bounds \
// RUN:           --unfold-loops-for-dsa --simplify-pointer-loops  --horn-sea-dsa-split \
// RUN:           --dsa=sea-ci --horn-bv-use-write --bmc=mono --bound=5 \
// RUN:           --horn-gsa "%s" 2>&1 | OutputCheck %s
// CHECK: ^unsat$

extern void __VERIFIER_error(void) __attribute__((noreturn));
extern void __VERIFIER_assume(int);

#define sassert(X) if(!(X)){__VERIFIER_error();}
#define assume(X) __VERIFIER_assume(X)

extern int nd(void);
int s0 = 0; int s1 = 0; int s2 = 0; int s3 = 0; int s4 = 0;

int m0 = 0; int m1 = 0; int m2 = 0; 

int eax = 3; int ebx = 0; int ecx = 0; int edx = 0; 


void print_state(){
	printf("%seax: %d, ebx: %d, ecx: %d, edx: %d, ", "\x1B[32m", eax, ebx, ecx, edx);
	printf("[");
	printf("%d ", s0);
	printf("%d ", s1);
	printf("%d ", s2);
	printf("%d ", s3);
	printf("%d ", s4);
	printf("] ");

	printf("{");
	printf("%d ", m0);
	printf("%d ", m1);
	printf("%d ", m2);
	printf("}\n %s", "\x1B[0m");
}

int pop(){
	int reg = s4;
	s4 = s3;
	s3 = s2;
	s2 = s1;
	s1 = s0;
	s0 = -1;
	return reg;
}

void push(int val){
	s0 = s1;
	s1 = s2;
	s2 = s3;
	s3 = s4;
	s4 = val;
}

void push_mem(int address){
	int val = -1;
	assume(0<=address && address<=3);
	switch(address){
		case 0:
			val = m0;
			break;
		case 1:
			val = m1;
			break;
		case 2:
			val = m2;
			break;
		default:
			return;
	}
	s0 = s1;
	s1 = s2;
	s2 = s3;
	s3 = s4;
	s4 = val;
}

void move_mem_const(int address, int val){
	assume(0<=address && address<=3);
	switch(address){
		case 0:
			m0 = val;
			break;
		case 1:
			m1 = val;
			break;
		case 2:
			m2 = val;
			break;
		default:
			return;
	}
}

int move_reg_mem(int address){
	assume(0<=address && address<=3);
	switch(address){
		case 0:
			return s0;
			break;
		case 1:
			return s1;
			break;
		case 2:
			return s2;
			break;
	}
}

void add_to_pointer(int address, int val){
	assume(0<=address && address<=3);
	switch(address){
		case 0:
			m0+= val;
			break;
		case 1:
			m1+= val;
			break;
		case 2:
			m2+= val;
			break;
		default:
			return;
	}
}

int add_from_pointer(int reg, int address){
	assume(0<=address && address<=3);
	switch(address){
		case 0:
			return reg+m0;
			break;
		case 1:
			return reg+m1;
			break;
		case 2:
			return reg+m2;
			break;
	}
}

void not_implemented(){
    return;
}
//inc dword ptr [ecx] ; ret
void gadget_0(){
	printf("inc dword ptr [ecx] ; ret\n");
	add_to_pointer(ecx, 1);
	return;
}
//inc eax ; pop eax ; ret
void gadget_1(){
	printf("inc eax ; pop eax ; ret\n");
	eax++;
	eax = pop();
	return;
}
//inc eax ; push eax ; ret
void gadget_2(){
	printf("inc eax ; push eax ; ret\n");
	eax++;
	push(eax);
	return;
}
//inc eax ; ret
void gadget_3(){
	printf("inc eax ; ret\n");
	eax++;
	return;
}
//inc ebx ; ret
void gadget_4(){
	printf("inc ebx ; ret\n");
	ebx++;
	return;
}
//inc ecx ; ret
void gadget_5(){
	printf("inc ecx ; ret\n");
	ecx++;
	return;
}
//inc edx ; ret
void gadget_6(){
	printf("inc edx ; ret\n");
	edx++;
	return;
}
//mov dword ptr [eax], 2 ; xor eax, eax ; ret
void gadget_7(){
	printf("mov dword ptr [eax], 2 ; xor eax, eax ; ret\n");
	move_mem_const(eax, 2);
	eax = 0;
	return;
}
//mov dword ptr [edx], eax ; mov eax, edx ; ret
void gadget_8(){
	printf("mov dword ptr [edx], eax ; mov eax, edx ; ret\n");
	move_mem_const(edx, eax);
	return;
}
//mov dword ptr [edx], eax ; pop ebx ; ret
void gadget_9(){
	printf("mov dword ptr [edx], eax ; pop ebx ; ret\n");
	move_mem_const(edx, eax);
	ebx = pop();
	return;
}
//mov eax, 1 ; pop ebx ; ret
void gadget_10(){
	printf("mov eax, 1 ; pop ebx ; ret\n");
	ebx = pop();
	return;
}
//mov eax, 1 ; ret
void gadget_11(){
	printf("mov eax, 1 ; ret\n");
	return;
}
//pop eax ; ret
void gadget_12(){
	printf("pop eax ; ret\n");
	eax = pop();
	return;
}
//pop ebx ; pop edx ; ret
void gadget_13(){
	printf("pop ebx ; pop edx ; ret\n");
	ebx = pop();
	edx = pop();
	return;
}
//pop ebx ; xor eax, eax ; ret
void gadget_14(){
	printf("pop ebx ; xor eax, eax ; ret\n");
	ebx = pop();
	eax = 0;
	return;
}
//pop ecx ; pop ebx ; ret
void gadget_15(){
	printf("pop ecx ; pop ebx ; ret\n");
	ecx = pop();
	ebx = pop();
	return;
}
//pop edx ; ret
void gadget_16(){
	printf("pop edx ; ret\n");
	edx = pop();
	return;
}
//push eax ; ret
void gadget_17(){
	printf("push eax ; ret\n");
	push(eax);
	return;
}
//push ebx ; ret
void gadget_18(){
	printf("push ebx ; ret\n");
	push(ebx);
	return;
}
//push ecx ; ret
void gadget_19(){
	printf("push ecx ; ret\n");
	push(ecx);
	return;
}
//push edx ; ret
void gadget_20(){
	printf("push edx ; ret\n");
	push(edx);
	return;
}
//xor eax, eax ; pop ebx ; ret
void gadget_21(){
	printf("xor eax, eax ; pop ebx ; ret\n");
	eax = 0;
	ebx = pop();
	return;
}
//xor eax, eax ; ret
void gadget_22(){
	printf("xor eax, eax ; ret\n");
	eax = 0;
	return;
}
int main(){
	int choice = 0;
	int prev_choice = nd();

	print_state();
	//bounded
	for(int i =0; i< 10; i++){
		choice = nd();
		assume(choice>=0 && choice<23);

        	if(choice==0){
        		printf("0 \n");
        		//assume(prev_choice == 0 || prev_choice == 2 );
        		gadget_0();
        	}

        	if(choice==1){
        		printf("1 \n");
        		//assume(prev_choice == 2 );
        		gadget_1();
        	}

        	if(choice==2){
        		printf("2 \n");
        		//assume(prev_choice == 0 || prev_choice == 6 || prev_choice == 7 || prev_choice == 16 || prev_choice == 14 || prev_choice == 19 );
        		gadget_2();
        	}

        	if(choice==3){
        		printf("3 \n");
        		//assume(prev_choice == 1 || prev_choice == 4 || prev_choice == 7 );
        		gadget_3();
        	}

        	if(choice==4){
        		printf("4 \n");
        		//assume(prev_choice == 13 );
        		gadget_4();
        	}

        	if(choice==5){
        		printf("5 \n");
        		//assume(prev_choice == 3 || prev_choice == 4 || prev_choice == 5 || prev_choice == 15 );
        		gadget_5();
        	}

        	if(choice==6){
        		printf("6 \n");
        		//assume(prev_choice == 0 || prev_choice == 2 );
        		gadget_6();
        	}

        	if(choice==7){
        		printf("7 \n");
        		//assume(prev_choice == 5 );
        		gadget_7();
        	}

        	if(choice==8){
        		printf("8 \n");
        		//assume(prev_choice == 3 );
        		gadget_8();
        	}

        	if(choice==9){
        		printf("9 \n");
        		//assume(prev_choice == 2 );
        		gadget_9();
        	}

        	if(choice==10){
        		printf("10 \n");
        		//assume(prev_choice == 2 );
        		gadget_10();
        	}

        	if(choice==11){
        		printf("11 \n");
        		//assume(prev_choice == 0 );
        		gadget_11();
        	}

        	if(choice==12){
        		printf("12 \n");
        		//assume(prev_choice == 2 );
        		gadget_12();
        	}

        	if(choice==13){
        		printf("13 \n");
        		//assume(prev_choice == 5 );
        		gadget_13();
        	}

        	if(choice==14){
        		printf("14 \n");
        		//assume(prev_choice == 20 );
        		gadget_14();
        	}

        	if(choice==15){
        		printf("15 \n");
        		//assume(prev_choice == 2 );
        		gadget_15();
        	}

        	if(choice==16){
        		printf("16 \n");
        		//assume(prev_choice == 14 );
        		gadget_16();
        	}

        	if(choice==17){
        		printf("17 \n");
        		//assume(prev_choice == 8 || prev_choice == 12 );
        		gadget_17();
        	}

        	if(choice==18){
        		printf("18 \n");
        		//assume(prev_choice == 8 );
        		gadget_18();
        	}

        	if(choice==19){
        		printf("19 \n");
        		//assume(prev_choice == 2 );
        		gadget_19();
        	}

        	if(choice==20){
        		printf("20 \n");
        		//assume(prev_choice == 2 || prev_choice == 20 );
        		gadget_20();
        	}

        	if(choice==21){
        		printf("21 \n");
        		//assume(prev_choice == 14 );
        		gadget_21();
        	}

        	if(choice==22){
        		printf("22 \n");
        		//assume(prev_choice == 12 );
        		gadget_22();
        	}
		print_state();
		sassert(!(m0 == 3 && m1 == 2 && m2 == 0 && eax == 1 && ebx == 2 && ecx == 3 && edx == 4 ));
		prev_choice = choice;
	}
 	return 0;
}