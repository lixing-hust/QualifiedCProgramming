/*
Filter an input vector of strings only for ones that contain given substring
>>> filter_by_substring({}, "a")
{}
>>> filter_by_substring({"abc", "bacd", "cde", "vector"}, "a")
{"abc", "bacd", "vector"}
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef struct {
    char** data;
    int size;
} StrArray;

StrArray filter_by_substring(char** strings, int strings_size, const char* substring){
    StrArray out;
    out.size = 0;
    out.data = (char**)malloc((size_t)strings_size * sizeof(char*));
    if (out.data == NULL) return out;
    for (int i=0;i<strings_size;i++)
    {
        if (strstr(strings[i], substring)!=NULL)
            out.data[out.size++] = strings[i];
    }
    return out;
}

