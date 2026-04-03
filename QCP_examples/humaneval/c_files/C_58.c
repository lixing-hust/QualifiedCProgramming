/*
Return sorted unique common elements for two vectors.
>>> common({1, 4, 3, 34, 653, 2, 5}, {5, 7, 1, 5, 9, 653, 121})
{1, 5, 653}
>>> common({5, 3, 2, 8}, {3, 2})
{2, 3}

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

static int contains(const int* a, int n, int x) {
    for (int i = 0; i < n; i++) if (a[i] == x) return 1;
    return 0;
}

IntArray common(const int* l1, int l1_size, const int* l2, int l2_size){
    IntArray out;
    out.size = 0;
    out.data = (int*)malloc((size_t)l1_size * sizeof(int));
    if (out.data == NULL) return out;
    for (int i=0;i<l1_size;i++)
        if (!contains(out.data, out.size, l1[i]))
            if (contains(l2, l2_size, l1[i]))
                out.data[out.size++] = l1[i];
    qsort(out.data, (size_t)out.size, sizeof(int), cmp_int);
    return out;
}

