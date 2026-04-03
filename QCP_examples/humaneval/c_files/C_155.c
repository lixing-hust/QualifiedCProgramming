/*
Given an integer. return a vector that has the number of even && odd digits respectively.

 Example:
    even_odd_count(-12) ==> {1, 1}
    even_odd_count(123) ==> {1, 2}
*/
#include<stdio.h>
#include<math.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray even_odd_count(int num){
    int w = abs(num);
    int n1=0,n2=0;
    IntArray out;
    if (w == 0) n2 = 1;
    while (w > 0) {
        int d = w % 10;
        if (d % 2 == 1) n1 += 1;
        else n2 += 1;
        w /= 10;
    }
    out.data = (int*)malloc(2 * sizeof(int));
    out.size = 2;
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    out.data[0] = n2;
    out.data[1] = n1;
    return out;
}

