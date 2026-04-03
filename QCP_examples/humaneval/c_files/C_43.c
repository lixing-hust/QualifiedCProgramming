/*
pairs_sum_to_zero takes a vector of integers as an input.
it returns true if there are two distinct elements in the vector that
sum to zero, && false otherwise.
>>> pairs_sum_to_zero({1, 3, 5, 0})
false
>>> pairs_sum_to_zero({1, 3, -2, 1})
false
>>> pairs_sum_to_zero({1, 2, 3, 7})
false
>>> pairs_sum_to_zero({2, 4, -5, 3, 5, 7})
true
>>> pairs_sum_to_zero({1})
false
*/
#include<stdio.h>
#include<stddef.h>
#include<stdbool.h>
bool pairs_sum_to_zero(int* l, int l_size){
    for (int i=0;i<l_size;i++)
    for (int j=i+1;j<l_size;j++)
    if (l[i]+l[j]==0) return true;
    return false;
}

