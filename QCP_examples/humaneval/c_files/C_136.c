/*
Create a function that returns a vector (a, b), where "a" is
the largest of negative integers, && "b" is the smallest
of positive integers in a vector.
If there is no negative || positive integers, return them as 0.

Examples:
largest_smallest_integers({2, 4, 1, 3, 5, 7}) == {0, 1}
largest_smallest_integers({}) == {0,0}
largest_smallest_integers({0}) == {0,0}
*/
#include<stdio.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray largest_smallest_integers(const int* lst, int lst_size){
    int maxneg=0,minpos=0;
    IntArray out;
    for (int i=0;i<lst_size;i++)
    {
        if (lst[i]<0 && (maxneg==0 || lst[i]>maxneg)) maxneg=lst[i];
        if (lst[i]>0 && (minpos==0 || lst[i]<minpos)) minpos=lst[i];
    }
    out.data = (int*)malloc(2 * sizeof(int));
    out.size = 2;
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    out.data[0] = maxneg;
    out.data[1] = minpos;
    return out;
}

