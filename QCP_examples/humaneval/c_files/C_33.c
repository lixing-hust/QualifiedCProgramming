/*
This function takes a vector l && returns a vector l' such that
l' is identical to l in the indicies that are ! divisible by three, while its values at the indicies that are divisible by three are equal
to the values of the corresponding indicies of l, but sorted.
>>> sort_third({1, 2, 3})
{1, 2, 3}
>>> sort_third({5, 6, 3, 4, 8, 9, 2})
{2, 6, 3, 4, 8, 9, 5}
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

IntArray sort_third(const int* l, int l_size){
    IntArray out;
    int* third;
    int third_size;
    int i;
    out.size = l_size;
    out.data = (int*)malloc((size_t)l_size * sizeof(int));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    third_size = (l_size + 2) / 3;
    third = (int*)malloc((size_t)third_size * sizeof(int));
    if (third == NULL) {
        free(out.data);
        out.data = NULL;
        out.size = 0;
        return out;
    }
    for (i=0;i*3<l_size;i++)
        third[i] = l[i*3];

    qsort(third, (size_t)third_size, sizeof(int), cmp_int);

    for (i=0;i<l_size;i++)
    {
        if (i%3==0) {out.data[i] = third[i/3];}
        else out.data[i] = l[i];
    }
    free(third);
    return out;

}

