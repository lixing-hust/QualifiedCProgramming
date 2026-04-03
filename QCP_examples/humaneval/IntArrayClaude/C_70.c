/*
Given vector of integers, return vector in strange order.
Strange sorting, is when you start with the minimum value,
then maximum of the remaining integers, then minimum && so on.

Examples:
strange_sort_vector({1, 2, 3, 4}) == {1, 4, 2, 3}
strange_sort_vector({5, 5, 5, 5}) == {5, 5, 5, 5}
strange_sort_vector({}) == {}
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

IntArray strange_sort_list(const int* lst, int lst_size){
    IntArray out;
    int* sorted;
    out.size = lst_size;
    out.data = (int*)malloc((size_t)lst_size * sizeof(int));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    sorted = (int*)malloc((size_t)lst_size * sizeof(int));
    if (sorted == NULL) {
        free(out.data);
        out.data = NULL;
        out.size = 0;
        return out;
    }
    for (int i=0;i<lst_size;i++) sorted[i] = lst[i];
    qsort(sorted, (size_t)lst_size, sizeof(int), cmp_int);
    int l=0,r=lst_size-1;
    int k=0;
    while (l<r)
    {
        out.data[k++] = sorted[l];
        l+=1;
        out.data[k++] = sorted[r];
        r-=1;
    }
    if (l==r) out.data[k++] = sorted[l];
    free(sorted);
    return out;

}

