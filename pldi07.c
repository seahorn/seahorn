typedef struct list{
	struct list *Next;
	int Data;
} list;

int Global = 10;
void do_all(list *L, void (*FP)(int *)){
	do{
		FP(&L->Data);
		L = L->Next;
	}while(L);
}
void do_all2(list *L, void (*FP)(int *)){
	do{
		FP(&L->Data);
		L = L->Next;
	}while(L);
}
void addG(int *X){
	(*X)+=Global;
}

void subG(int *X){
	(*X)-=Global;
}

void addGToList(list *L){
	do_all(L, addG);
}


list *makeList(int Num){
	list *New = malloc(sizeof(list));
	New->Next = Num? makeList(Num-1):0;
	New->Data = Num;
	return New;
}

int main(){
	list *X = makeList(10);
	list *Y = makeList(100);
	
	addGToList(X);
	Global = 20;
	addGToList(Y);
	do_all2(X, subG);
}
