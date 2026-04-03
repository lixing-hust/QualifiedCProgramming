/*
Return vector with elements incremented by 1.
>>> incr_vector({1, 2, 3})
{2, 3, 4}
>>> incr_vector({5, 3, 5, 2, 3, 3, 9, 0, 123})
{6, 4, 6, 3, 4, 4, 10, 1, 124}
*/
#include<stdio.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray incr_list(const int* l, int l_size){
    IntArray out;
    out.data = (int*)malloc((size_t)l_size * sizeof(int));
    out.size = l_size;
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    for (int i=0;i<l_size;i++)
        out.data[i]=l[i]+1;
    return out;
}

