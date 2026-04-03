/*
For a given string, flip lowercase characters to uppercase && uppercase to lowercase.
>>> flip_case("Hello")
"hELLO"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
char* filp_case(const char* str){
    size_t i;
    size_t n = strlen(str);
    char* out = (char*)malloc(n + 1);

    if (out == NULL) {
        return NULL;
    }

    for (i = 0; i < n; i++) {
        char w = str[i];
        if (w >= 'a' && w <= 'z') {
            w = (char)(w - ('a' - 'A'));
        } else if (w >= 'A' && w <= 'Z') {
            w = (char)(w + ('a' - 'A'));
        }
        out[i] = w;
    }
    out[n] = '\0';
    return out;
}

