/*
Circular shift the digits of the integer x, shift the digits right by shift
&& return the result as a string.
If shift > number of digits, return digits reversed.
>>> circular_shift(12, 1)
"21"
>>> circular_shift(12, 2)
"12"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
char* circular_shift(int x, int shift){
    char buf[64];
    int n;
    char* out;
    sprintf(buf, "%d", x);
    n = (int)strlen(buf);
    out = (char*)malloc((size_t)n + 1);
    if (out == NULL) return NULL;
    if (n < shift)
    {
        for (int i = 0; i < n; i++) out[i] = buf[n - 1 - i];
        out[n] = '\0';
        return out;
    }
    for (int i = 0; i < n; i++) {
        int src = (n - shift + i) % n;
        out[i] = buf[src];
    }
    out[n] = '\0';
    return out;
}

