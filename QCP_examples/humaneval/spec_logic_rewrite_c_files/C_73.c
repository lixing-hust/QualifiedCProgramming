/*
Given a vector arr of integers, find the minimum number of elements that
need to be changed to make the vector palindromic. A palindromic vector is a vector that
is read the same backwards && forwards. In one change, you can change one element to any other element.

For example:
smallest_change({1,2,3,5,4,7,9,6}) == 4
smallest_change({1, 2, 3, 4, 3, 2, 2}) == 1
smallest_change({1, 2, 3, 2, 1}) == 0
*/
#include<stdio.h>
#include<stddef.h>
int smallest_change(int* arr, int arr_size){
    int out=0;
    for (int i=0;i<arr_size-1-i;i++)
        if (arr[i]!=arr[arr_size-1-i])
            out+=1;
    return out;
}

