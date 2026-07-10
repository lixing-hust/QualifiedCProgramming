/*
Given a vector of positive integers x. return a sorted vector of all 
elements that hasn't any even digit.

Note: Returned vector should be sorted in increasing order.

For example:
>>> unique_digits({15, 33, 1422, 1})
{1, 15, 33}
>>> unique_digits({152, 323, 1422, 10})
{}
*/
#include<stdio.h>
#include<stdlib.h>
#include<stdbool.h>

typedef struct {
    int* data;
    int size;
} IntArray;

static int cmp_int(const void* a, const void* b) {
    int x = *(const int*)a;
    int y = *(const int*)b;
    return (x > y) - (x < y);
}

IntArray unique_digits(const int* x, int x_size){
    IntArray out;
    out.size = 0;
    out.data = (int*)malloc((size_t)x_size * sizeof(int));
    if (out.data == NULL) return out;
    for (int i=0;i<x_size;i++)
        {
            int num=x[i];
            bool u=true;
            if (num==0) u=false;
            while (num>0 && u)
            {
                if (num%2==0) u=false;
                num=num/10;
            }
            if (u) out.data[out.size++] = x[i];
        }
    qsort(out.data, (size_t)out.size, sizeof(int), cmp_int);
    return out;
}

