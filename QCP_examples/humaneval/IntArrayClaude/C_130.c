/*
Everyone knows Fibonacci sequence, it was studied deeply by mathematicians in 
the last couple centuries. However, what people don't know is Tribonacci sequence.
Tribonacci sequence is defined by the recurrence:
tri(1) = 3
tri(n) = 1 + n / 2, if n is even.
tri(n) =  tri(n - 1) + tri(n - 2) + tri(n + 1), if n is odd.
For example:
tri(2) = 1 + (2 / 2) = 2
tri(4) = 3
tri(3) = tri(2) + tri(1) + tri(4)
       = 2 + 3 + 3 = 8 
You are given a non-negative integer number n, you have to a return a vector of the 
first n + 1 numbers of the Tribonacci sequence.
Examples:
tri(3) = {1, 3, 2, 8}
*/
#include<stdio.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray tri(int n){
    IntArray out;
    out.size = n + 1;
    out.data = (int*)malloc((size_t)(n + 1) * sizeof(int));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    out.data[0] = 1;
    if (n==0) return out;
    out.data[1] = 3;
    for (int i=2;i<=n;i++)
    {
        if (i%2==0) out.data[i] = 1+i/2;
        else out.data[i] = out.data[i-1]+out.data[i-2]+1+(i+1)/2;
    }
    return out;
}

