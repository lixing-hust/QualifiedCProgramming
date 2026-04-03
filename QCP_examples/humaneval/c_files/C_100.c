/*
Given a positive integer n, you have to make a pile of n levels of stones.
The first level has n stones.
The number of stones in the next level is:
    - the next odd number if n is odd.
    - the next even number if n is even.
Return the number of stones in each level in a vector, where element at index
i represents the number of stones in the level (i+1).

Examples:
>>> make_a_pile(3)
{3, 5, 7}
*/
#include<stdio.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray make_a_pile(int n){
    IntArray out;
    out.size = n;
    out.data = (int*)malloc((size_t)n * sizeof(int));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    out.data[0] = n;
    for (int i=1;i<n;i++)
        out.data[i] = out.data[i-1] + 2;
    return out;
}

