/*
Concatenate vector of strings into a single string
>>> concatenate({})
""
>>> concatenate({"a", "b", "c"})
"abc"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

char* concatenate(char** strings, int strings_size){
    int total = 1;
    char* out;
    int k = 0;
    for (int i=0;i<strings_size;i++) total += (int)strlen(strings[i]);
    out = (char*)malloc((size_t)total);
    if (out == NULL) return NULL;
    for (int i=0;i<strings_size;i++) {
        int len = (int)strlen(strings[i]);
        memcpy(out + k, strings[i], (size_t)len);
        k += len;
    }
    out[k] = '\0';
    return out;
}

