/*
Given a positive integer n, return a sorted vector that has the odd numbers in collatz sequence.

The Collatz conjecture is a conjecture in mathematics that concerns a sequence defined
as follows: start with any positive integer n. Then each term is obtained from the 
previous term as follows: if the previous term is even, the next term is one half of 
the previous term. If the previous term is odd, the next term is 3 times the previous
term plus 1. The conjecture is that no matter what value of n, the sequence will always reach 1.

Note: 
    1. Collatz(1) is {1}.
    2. returned vector sorted in increasing order.

For example:
get_odd_collatz(5) returns {1, 5} // The collatz sequence for 5 is {5, 16, 8, 4, 2, 1}, so the odd numbers are only 1, && 5.
*/
#include<stdio.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

static int cmp_int(const void* a, const void* b) {
    int x = *(const int*)a;
    int y = *(const int*)b;
    return (x > y) - (x < y);
}

IntArray get_odd_collatz(int n){
    IntArray out;
    int cap = 16;
    out.size = 0;
    out.data = (int*)malloc((size_t)cap * sizeof(int));
    if (out.data == NULL) return out;
    out.data[out.size++] = 1;
    while (n!=1)
    {
        if (n%2==1) {
            if (out.size == cap) {
                int new_cap = cap * 2;
                int* tmp = (int*)realloc(out.data, (size_t)new_cap * sizeof(int));
                if (tmp == NULL) break;
                out.data = tmp;
                cap = new_cap;
            }
            out.data[out.size++] = n;
            n=n*3+1;
        }
        else n=n/2;
    }
    qsort(out.data, (size_t)out.size, sizeof(int), cmp_int);
    return out;
}

