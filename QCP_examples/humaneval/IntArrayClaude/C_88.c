/*
Given a vector of non-negative integers, return a copy of the given vector after sorting,
you will sort the given vector in ascending order if the sum( first index value, last index value) is odd,
|| sort it in descending order if the sum( first index value, last index value) is even.

Note:
* don't change the given vector.

Examples:
* sort_vector({}) => {}
* sort_vector({5}) => {5}
* sort_vector({2, 4, 3, 0, 1, 5}) => {0, 1, 2, 3, 4, 5}
* sort_vector({2, 4, 3, 0, 1, 5, 6}) => {6, 5, 4, 3, 2, 1, 0}
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

IntArray sort_array(const int* array, int array_size){
    IntArray out;
    out.size = array_size;
    if (array_size==0) {
        out.data = NULL;
        return out;
    }
    out.data = (int*)malloc((size_t)array_size * sizeof(int));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    for (int i=0;i<array_size;i++) out.data[i] = array[i];
    qsort(out.data, (size_t)array_size, sizeof(int), cmp_int);
    if ((array[0]+array[array_size-1]) %2==0)
    {
        for (int i=0;i<array_size/2;i++) {
            int t = out.data[i];
            out.data[i] = out.data[array_size-1-i];
            out.data[array_size-1-i] = t;
        }
    }
    return out;

}

