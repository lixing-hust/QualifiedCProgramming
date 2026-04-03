/*
Write a function that returns true if the object q will fly, && false otherwise.
The object q will fly if it's balanced (it is a palindromic vector) && the sum of its elements is less than || equal the maximum possible weight w.

Example:
will_it_fly({1, 2}, 5) ➞ false 
// 1+2 is less than the maximum possible weight, but it's unbalanced.

will_it_fly({3, 2, 3}, 1) ➞ false
// it's balanced, but 3+2+3 is more than the maximum possible weight.

will_it_fly({3, 2, 3}, 9) ➞ true
// 3+2+3 is less than the maximum possible weight, && it's balanced.

will_it_fly({3}, 5) ➞ true
// 3 is less than the maximum possible weight, && it's balanced.
*/
#include<stdio.h>
#include<stddef.h>
#include<stdbool.h>
bool will_it_fly(int* q, int q_size, int w){
    int sum=0;
    for (int i=0;i<q_size;i++)
    {
        if (q[i]!=q[q_size-1-i]) return false;
        sum+=q[i];
    }
    if (sum>w) return false;
    return true;
}

