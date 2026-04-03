/*
From a given vector of integers, generate a vector of rolling maximum element found until given moment
in the sequence.
>>> rolling_max({1, 2, 3, 2, 3, 4, 2})
{1, 2, 3, 3, 3, 4, 4}
*/
#include<stdio.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray rolling_max(const int* numbers, int numbers_size){
    IntArray out;
    out.size = numbers_size;
    out.data = (int*)malloc((size_t)numbers_size * sizeof(int));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    int max=0;
    for (int i=0;i<numbers_size;i++)
    {
        if (numbers[i]>max) max=numbers[i];
        out.data[i] = max;
    }
    return out;
}

