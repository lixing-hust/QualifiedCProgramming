/*
Return a string containing space-delimited numbers starting from 0 upto n inclusive.
>>> string_sequence(0)
"0"
>>> string_sequence(5)
"0 1 2 3 4 5"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
char* string_sequence(int n){
    int total = 2;
    char tmp[32];
    char* out;
    int k = 0;
    for (int i=1;i<=n;i++) {
        sprintf(tmp, "%d", i);
        total += 1 + (int)strlen(tmp);
    }
    out = (char*)malloc((size_t)total);
    if (out == NULL) return NULL;
    out[k++]='0';
    for (int i=1;i<=n;i++) {
        int len;
        out[k++]=' ';
        sprintf(tmp, "%d", i);
        len = (int)strlen(tmp);
        memcpy(out + k, tmp, (size_t)len);
        k += len;
    }
    out[k]='\0';
    return out;
}

