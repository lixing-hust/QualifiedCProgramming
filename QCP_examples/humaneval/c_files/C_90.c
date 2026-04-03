/*
You are given a vector of integers.
Write a function next_smallest() that returns the 2nd smallest element of the vector.
Return None if there is no such element.

next_smallest({1, 2, 3, 4, 5}) == 2
next_smallest({5, 1, 4, 3, 2}) == 2
next_smallest({}) == None
next_smallest({1, 1}) == None
*/
#include<stdio.h>
#include<stddef.h>
#include<stdlib.h>

static int cmp_int(const void* a, const void* b){
    int ia = *(const int*)a;
    int ib = *(const int*)b;
    return (ia > ib) - (ia < ib);
}

int next_smallest(int* lst, int lst_size){
    qsort(lst, (size_t)lst_size, sizeof(int), cmp_int);
    for (int i=1;i<lst_size;i++)
        if (lst[i]!=lst[i-1]) return lst[i];
    return -1;
}

