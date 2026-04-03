#include<stdio.h>
#include<stdlib.h>
#include<string.h>
char* encode_shift(const char* s){
    // returns encoded string by shifting every character by 5 in the alphabet.
    size_t i;
    size_t n = strlen(s);
    char* out = (char*)malloc(n + 1);

    if (out == NULL) {
        return NULL;
    }

    for (i = 0; i < n; i++) {
        int w = ((int)s[i] + 5 - (int)'a') % 26 + (int)'a';
        out[i] = (char)w;
    }
    out[n] = '\0';
    return out;
}
char* decode_shift(const char* s){
    // takes as input string encoded with encode_shift function. Returns decoded string.
    size_t i;
    size_t n = strlen(s);
    char* out = (char*)malloc(n + 1);

    if (out == NULL) {
        return NULL;
    }

    for (i = 0; i < n; i++) {
        int w = ((int)s[i] + 21 - (int)'a') % 26 + (int)'a';
        out[i] = (char)w;
    }
    out[n] = '\0';
    return out;
}

