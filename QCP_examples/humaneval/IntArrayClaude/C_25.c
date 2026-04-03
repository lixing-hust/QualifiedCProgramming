/*
Return vector of prime factors of given integer in the order from smallest to largest.
Each of the factors should be vectored number of times corresponding to how many times it appeares in factorization.
Input number should be equal to the product of all factors
>>> factorize(8)
{2, 2, 2}
>>> factorize(25)
{5, 5}
>>> factorize(70)
{2, 5, 7}
*/
#include<stdio.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray factorize(int n){
    IntArray out;
    out.size = 0;
    out.data = (int*)malloc((size_t)n * sizeof(int));
    if (out.data == NULL) {
        return out;
    }
    for (int i=2;i*i<=n;i++)
        if (n%i==0)
        {
            n=n/i;
            out.data[out.size++] = i;
            i-=1;
        }
    out.data[out.size++] = n;
    return out;
}

