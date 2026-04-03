/*
Return true if all numbers in the vector l are below threshold t.
>>> below_threshold({1, 2, 4, 10}, 100)
true
>>> below_threshold({1, 20, 4, 10}, 5)
false
*/
#include<stdio.h>
#include<stddef.h>
#include<stdbool.h>
bool below_threshold(int* l, int l_size, int t){
    for (int i=0;i<l_size;i++)
        if (l[i]>=t) return false;
    return true;
}

