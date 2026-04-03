/*
triples_sum_to_zero takes a vector of integers as an input.
it returns true if there are three distinct elements in the vector that
sum to zero, && false otherwise.

>>> triples_sum_to_zero({1, 3, 5, 0})
false
>>> triples_sum_to_zero({1, 3, -2, 1})
true
>>> triples_sum_to_zero({1, 2, 3, 7})
false
>>> triples_sum_to_zero({2, 4, -5, 3, 9, 7})
true
>>> triples_sum_to_zero({1})
false
*/
#include<stdio.h>
#include<stddef.h>
#include<stdbool.h>
bool triples_sum_to_zero(int* l, int l_size){
    for (int i=0;i<l_size;i++)
    for (int j=i+1;j<l_size;j++)
    for (int k=j+1;k<l_size;k++)
        if (l[i]+l[j]+l[k]==0) return true;
    return false;
}

