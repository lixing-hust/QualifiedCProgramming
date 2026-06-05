/*
Write a function that accepts a vector of strings as a parameter,
deletes the strings that have odd lengths from it,
&& returns the resulted vector with a sorted order,
The vector is always a vector of strings && never a vector of numbers,
&& it may contain duplicates.
The order of the vector should be ascending by length of each word, && you
should return the vector sorted by that rule.
If two words have the same length, sort the vector alphabetically.
The function should return a vector of strings in sorted order.
You may assume that all words will have the same length.
For example:
assert vector_sort({"aa", "a", "aaa"}) => {"aa"}
assert vector_sort({"ab", "a", "aaa", "cd"}) => {"ab", "cd"}
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef struct {
    char** data;
    int size;
} StrArray;

static int cmp_word(const void* a, const void* b) {
    const char* x = *(const char**)a;
    const char* y = *(const char**)b;
    int lx = (int)strlen(x);
    int ly = (int)strlen(y);
    if (lx != ly) return lx - ly;
    return strcmp(x, y);
}

StrArray sorted_list_sum(char** lst, int lst_size){
    StrArray out;
    out.size = 0;
    out.data = (char**)malloc((size_t)lst_size * sizeof(char*));
    if (out.data == NULL) return out;
    for (int i=0;i<lst_size;i++)
    if ((int)strlen(lst[i])%2==0) out.data[out.size++] = lst[i];
    qsort(out.data, (size_t)out.size, sizeof(char*), cmp_word);
    return out;
}

