/*
remove_vowels is a function that takes string && returns string without vowels.
>>> remove_vowels("")
""
>>> remove_vowels("abcdef\nghijklm")
"bcdf\nghjklm"
>>> remove_vowels("abcdef")
"bcdf"
>>> remove_vowels("aaaaa")
""
>>> remove_vowels("aaBAA")
"B"
>>> remove_vowels("zbcd")
"zbcd"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
char* remove_vowels(const char* text){
    const char* vowels = "AEIOUaeiou";
    size_t i;
    size_t j = 0;
    size_t n = strlen(text);
    char* out = (char*)malloc(n + 1);

    if (out == NULL) {
        return NULL;
    }

    for (i = 0; i < n; i++) {
        if (strchr(vowels, text[i]) == NULL) {
            out[j++] = text[i];
        }
    }
    out[j] = '\0';
    return out;

}

