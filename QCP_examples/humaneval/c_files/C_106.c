/*
Implement the function f that takes n as a parameter,
&& returns a vector of size n, such that the value of the element at index i is the factorial of i if i is even
|| the sum of numbers from 1 to i otherwise.
i starts from 1.
the factorial of i is the multiplication of the numbers from 1 to i (1 * 2 * ... * i).
Example:
f(5) == {1, 2, 6, 24, 15}
*/
#include<stdio.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray f(int n){
    int sum=0,prod=1;
    IntArray out;
    out.size = n;
    out.data = (int*)malloc((size_t)n * sizeof(int));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    for (int i=1;i<=n;i++)
    {
        sum+=i;
        prod*=i;
        if (i%2==0) out.data[i-1] = prod;
        else out.data[i-1] = sum;
    } 
    return out;
}

