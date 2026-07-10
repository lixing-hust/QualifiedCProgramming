/*
Filter an input vector of strings only for ones that start with a given prefix.
>>> filter_by_prefix({}, "a")
{}
>>> filter_by_prefix({"abc", "bcd", "cde", "vector"}, "a")
{"abc", "vector"}
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef struct {
    char** data;
    int size;
} StrArray;

StrArray filter_by_prefix(char** strings, int strings_size, const char* prefix){
    StrArray out;
    int plen = (int)strlen(prefix);
    out.size = 0;
    out.data = (char**)malloc((size_t)strings_size * sizeof(char*));
    if (out.data == NULL) return out;
    for (int i=0;i<strings_size;i++)
        if (strncmp(strings[i], prefix, (size_t)plen)==0) out.data[out.size++] = strings[i];
    return out;
}

