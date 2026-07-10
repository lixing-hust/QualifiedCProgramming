/*
Write a function that takes a vector of numbers as input && returns 
the number of elements in the vector that are greater than 10 && both 
first && last digits of a number are odd (1, 3, 5, 7, 9).
For example:
specialFilter({15, -73, 14, -15}) => 1 
specialFilter({33, -2, -3, 45, 21, 109}) => 2
*/
#include<stdio.h>
#include<stddef.h>
#include<string.h>
int specialFilter(int* nums, int nums_size){
    int num=0;
    for (int i=0;i<nums_size;i++)
    if (nums[i]>10)
    {
        int first = nums[i];
        int last = nums[i] % 10;
        while (first >= 10) {
            first /= 10;
        }
        if (first % 2 == 1 && last % 2 == 1) num+=1;
    }
    return num;
}

