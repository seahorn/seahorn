#include "seahorn/seahorn.h"
extern int nd(void);
int s0 = 0; int s1 = 0; int s2 = 0; int s3 = 0; int s4 = 0; 

int m0 = 0; int m1 = 0; int m2 = 0; 

int eax = 0; int ebx = 0; int ecx = 0; int edx = 0; 


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
        		if(prev_choice == 0 || prev_choice == 2 ){
        			printf("0 \n");
        			gadget_0();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==1){
        		if(prev_choice == 2 ){
        			printf("1 \n");
        			gadget_1();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==2){
        		if(prev_choice == 0 || prev_choice == 6 || prev_choice == 7 || prev_choice == 16 || prev_choice == 14 || prev_choice == 19 ){
        			printf("2 \n");
        			gadget_2();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==3){
        		if(prev_choice == 1 || prev_choice == 4 || prev_choice == 7 ){
        			printf("3 \n");
        			gadget_3();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==4){
        		if(prev_choice == 13 ){
        			printf("4 \n");
        			gadget_4();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==5){
        		if(prev_choice == 3 || prev_choice == 4 || prev_choice == 5 || prev_choice == 15 ){
        			printf("5 \n");
        			gadget_5();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==6){
        		if(prev_choice == 0 || prev_choice == 2 ){
        			printf("6 \n");
        			gadget_6();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==7){
        		if(prev_choice == 5 ){
        			printf("7 \n");
        			gadget_7();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==8){
        		if(prev_choice == 3 ){
        			printf("8 \n");
        			gadget_8();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==9){
        		if(prev_choice == 2 ){
        			printf("9 \n");
        			gadget_9();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==10){
        		if(prev_choice == 2 ){
        			printf("10 \n");
        			gadget_10();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==11){
        		if(prev_choice == 0 ){
        			printf("11 \n");
        			gadget_11();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==12){
        		if(prev_choice == 2 ){
        			printf("12 \n");
        			gadget_12();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==13){
        		if(prev_choice == 5 ){
        			printf("13 \n");
        			gadget_13();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==14){
        		if(prev_choice == 20 ){
        			printf("14 \n");
        			gadget_14();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==15){
        		if(prev_choice == 2 ){
        			printf("15 \n");
        			gadget_15();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==16){
        		if(prev_choice == 14 ){
        			printf("16 \n");
        			gadget_16();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==17){
        		if(prev_choice == 8 || prev_choice == 12 ){
        			printf("17 \n");
        			gadget_17();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==18){
        		if(prev_choice == 8 ){
        			printf("18 \n");
        			gadget_18();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==19){
        		if(prev_choice == 2 ){
        			printf("19 \n");
        			gadget_19();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==20){
        		if(prev_choice == 2 || prev_choice == 20 ){
        			printf("20 \n");
        			gadget_20();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==21){
        		if(prev_choice == 14 ){
        			printf("21 \n");
        			gadget_21();
        		}else{
        			return 0;
        		}
        	}

        	if(choice==22){
        		if(prev_choice == 12 ){
        			printf("22 \n");
        			gadget_22();
        		}else{
        			return 0;
        		}
        	}
		print_state();
		sassert(!(eax == 2 && ebx == 4 && ecx == 3 ));
		prev_choice = choice;
	}
 	return 0;
}