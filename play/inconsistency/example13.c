/*
http://stackoverflow.com/questions/10248705/segmentation-fault-while-matrix-multiplication-c
*/

#include<stdio.h>
#include<stdlib.h>


int main(){
    int **matrix;
    int A, B, i, j;
    A = 1;
    B = 3;

    matrix=(int**)malloc(sizeof(int*)*B);
        for(i=0;i<A;i++)
            (matrix)[i]=(int*)malloc(sizeof(int)*A);

    for(i=0;i<B;i++)
    {
        for(j=0;j<A;j++)
            {    
                 
                 /* The problem is that matrix[i] is not initialized 
                   for any i>=A but how do I express that with seahorn?
                 */
                 matrix[i][j] = 3;
            }
    }

    return 0;
}
