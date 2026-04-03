/*
Insert a number "delimeter" between every two consecutive elements of input vector `numbers"
>>> intersperse({}, 4)
{}
>>> intersperse({1, 2, 3}, 4)
{1, 4, 2, 4, 3}
*/
#include<stdio.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray intersperse(const int* numbers, int numbers_size, int delimeter){
    IntArray out;
    int k = 0;
    if (numbers_size == 0) {
        out.data = NULL;
        out.size = 0;
        return out;
    }
    out.size = numbers_size * 2 - 1;
    out.data = (int*)malloc((size_t)out.size * sizeof(int));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    out.data[k++] = numbers[0];
    for (int i=1;i<numbers_size;i++)
    {
        out.data[k++] = delimeter;
        out.data[k++] = numbers[i];

    }
    return out;
}

