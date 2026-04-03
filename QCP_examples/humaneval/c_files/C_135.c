/*
Create a function which returns the largest index of an element which
is ! greater than || equal to the element immediately preceding it. If
no such element exists then return -1. The given vector will ! contain
duplicate values.

Examples:
can_arrange({1,2,4,3,5}) = 3
can_arrange({1,2,3}) = -1
*/
#include<stdio.h>
#include<stddef.h>
int can_arrange(int* arr, int arr_size){
    int max=-1;
    for (int i=0;i<arr_size;i++)
    if (arr[i]<=i) max=i;
    return max;
}

