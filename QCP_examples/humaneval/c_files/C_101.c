/*
You will be given a string of words separated by commas || spaces. Your task is
to split the string into words && return a vector of the words.

For example:
words_string("Hi, my name is John") == {"Hi", "my", "name", "is", "John"}
words_string("One, two, three, four, five, six") == {"One", 'two", 'three", "four", "five", 'six"}
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef struct {
    char** data;
    int size;
} StrArray;

StrArray words_string(const char* s){
    StrArray out;
    int cap = 8;
    int start = -1;
    int n = (int)strlen(s);
    out.size = 0;
    out.data = (char**)malloc((size_t)cap * sizeof(char*));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    for (int i=0;i<=n;i++) {
        char ch = (i < n) ? s[i] : ' ';
        if (ch==' ' || ch==',') {
            if (start >= 0) {
                int len = i - start;
                char* w = (char*)malloc((size_t)len + 1);
                if (w == NULL) return out;
                memcpy(w, s + start, (size_t)len);
                w[len] = '\0';
                if (out.size == cap) {
                    int new_cap = cap * 2;
                    char** tmp = (char**)realloc(out.data, (size_t)new_cap * sizeof(char*));
                    if (tmp == NULL) return out;
                    out.data = tmp;
                    cap = new_cap;
                }
                out.data[out.size++] = w;
                start = -1;
            }
        } else if (start < 0) {
            start = i;
        }
    }
    return out;
}

