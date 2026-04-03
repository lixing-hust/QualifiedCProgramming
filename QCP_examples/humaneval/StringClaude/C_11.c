/*
Input are two strings a && b consisting only of 1s && 0s.
Perform binary XOR on these inputs && return result also as a string.
>>> string_xor("010", "110")
"100"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
char* string_xor(const char* a, const char* b){
    size_t i;
    size_t n1 = strlen(a);
    size_t n2 = strlen(b);
    size_t n = n1 < n2 ? n1 : n2;
    char* output = (char*)malloc(n + 1);

    if (output == NULL) {
        return NULL;
    }

    for (i = 0; i < n; i++) {
        output[i] = (a[i] == b[i]) ? '0' : '1';
    }
    output[n] = '\0';
    return output;
}

