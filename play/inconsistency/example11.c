//from wikipedia

#include <stdio.h>

int main(void)
{
	int SIZE =20;
	int a[SIZE];
	for (int i=0; i<SIZE; i++) {
		a[i] = i;
	}

	//this is a very simplified version
	//of an inconsistency that you should
	//get when you try to sort an array
	//twice.
	if (a[1]>a[3]) {
		//unreachable
		return 1;
	}
	return 0;
}
