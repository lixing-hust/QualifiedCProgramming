/*
From a vector of integers, remove all elements that occur more than once.
Keep order of elements left the same as in the input.
>>> remove_duplicates({1, 2, 3, 2, 4})
{1, 3, 4}
*/
#include<stdio.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

static int contains(const int* a, int n, int x) {
    for (int i = 0; i < n; i++) if (a[i] == x) return 1;
    return 0;
}

IntArray remove_duplicates(const int* numbers, int numbers_size){
    IntArray out;
    int* has1;
    int has1_size = 0;
    int* has2;
    int has2_size = 0;

    out.size = 0;
    out.data = (int*)malloc((size_t)numbers_size * sizeof(int));
    has1 = (int*)malloc((size_t)numbers_size * sizeof(int));
    has2 = (int*)malloc((size_t)numbers_size * sizeof(int));
    if (out.data == NULL || has1 == NULL || has2 == NULL) {
        free(out.data);
        free(has1);
        free(has2);
        out.data = NULL;
        out.size = 0;
        return out;
    }

    for (int i=0;i<numbers_size;i++)
    {
        if (contains(has2, has2_size, numbers[i])) continue;
        if (contains(has1, has1_size, numbers[i])) {
            has2[has2_size++] = numbers[i];
        } else {
            has1[has1_size++] = numbers[i];
        }
    }
    for (int i=0;i<numbers_size;i++)
    if (!contains(has2, has2_size, numbers[i]))
        out.data[out.size++] = numbers[i];

    free(has1);
    free(has2);
    return out;


}

