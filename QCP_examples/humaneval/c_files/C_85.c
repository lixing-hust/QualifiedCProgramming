/*
Given a non-empty vector of integers lst. add the even elements that are at odd indices..


Examples:
    add({4, 2, 6, 7}) ==> 2 
*/
#include<stdio.h>
#include<stddef.h>
int add(int* lst, int lst_size){
    int sum=0;
    for (int i=0;i*2+1<lst_size;i++)
        if (lst[i*2+1]%2==0) sum+=lst[i*2+1];
    return sum;
}

