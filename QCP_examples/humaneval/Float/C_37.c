/*
This function takes a vector l && returns a vector l' such that
l' is identical to l in the odd indicies, while its values at the even indicies are equal
to the values of the even indicies of l, but sorted.
>>> sort_even({1, 2, 3})
{1, 2, 3}
>>> sort_even({5, 6, 3, 4})
{3, 6, 5, 4}
*/
#include<stdio.h>
#include<math.h>
#include<stdlib.h>

typedef struct {
    float* data;
    int size;
} FloatArray;

static int cmp_float(const void* a, const void* b) {
    float x = *(const float*)a;
    float y = *(const float*)b;
    return (x > y) - (x < y);
}

FloatArray sort_even(const float* l, int l_size){
    FloatArray out;
    float* even;
    int even_size = (l_size + 1) / 2;
    out.size = l_size;
    out.data = (float*)malloc((size_t)l_size * sizeof(float));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    even = (float*)malloc((size_t)even_size * sizeof(float));
    if (even == NULL) {
        free(out.data);
        out.data = NULL;
        out.size = 0;
        return out;
    }
    for (int i=0;i*2<l_size;i++)
        even[i] = l[i*2];
    qsort(even, (size_t)even_size, sizeof(float), cmp_float);
    for (int i=0;i<l_size;i++)
    {
        if (i%2==0) out.data[i] = even[i/2];
        if (i%2==1) out.data[i] = l[i];
    }
    free(even);
    return out;
}

