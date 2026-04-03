/*
In this Kata, you have to sort a vector of non-negative integers according to
number of ones in their binary representation in ascending order.
For similar number of ones, sort based on decimal value.

It must be implemented like this:
>>> sort_vector({1, 5, 2, 3, 4}) == {1, 2, 3, 4, 5}
>>> sort_vector({-2, -3, -4, -5, -6}) == {-6, -5, -4, -3, -2}
>>> sort_vector({1, 0, 2, 3, 4}) == {0, 1, 2, 3, 4}
*/
#include<stdio.h>
#include<math.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray sort_array(const int* arr, int arr_size){
    IntArray out;
    int* bin;
    int m;

    out.size = arr_size;
    out.data = (int*)malloc((size_t)arr_size * sizeof(int));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    for (int i = 0; i < arr_size; i++) {
        out.data[i] = arr[i];
    }

    bin = (int*)malloc((size_t)arr_size * sizeof(int));
    if (bin == NULL) {
        free(out.data);
        out.data = NULL;
        out.size = 0;
        return out;
    }

    for (int i=0;i<arr_size;i++)
    {
        int b=0,n=abs(out.data[i]);
        while (n>0)
        {
            b+=n%2;n=n/2;
        }
        bin[i] = b;
    }
    for (int i=0;i<arr_size;i++)
    for (int j=1;j<arr_size;j++)
    if (bin[j]<bin[j-1] || (bin[j]==bin[j-1] && out.data[j]<out.data[j-1]))
    {
        m=out.data[j];out.data[j]=out.data[j-1];out.data[j-1]=m;
        m=bin[j];bin[j]=bin[j-1];bin[j-1]=m;
    }
    free(bin);
    return out;
}

