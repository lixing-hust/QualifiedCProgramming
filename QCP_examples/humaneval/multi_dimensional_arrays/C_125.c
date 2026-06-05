/*
Given a string of words, return a vector of words split on whitespace, if no whitespaces exists in the text you
should split on commas ',' if no commas exists you should return a vector with one element, the number of lower-case letters with odd order in the
alphabet, ord("a") = 0, ord("b") = 1, ... ord("z") = 25
Examples
split_words("Hello world!") ➞ {"Hello", "world!"}
split_words("Hello,world!") ➞ {"Hello", "world!"}
split_words("abcdef") == {"3"} 
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef struct {
    char** data;
    int size;
} StrArray;

StrArray split_words(const char* txt){
    StrArray out;
    int cap = 8;
    int n = (int)strlen(txt);
    int has_space = strchr(txt, ' ') != NULL;
    int has_comma = strchr(txt, ',') != NULL;
    char sep = has_space ? ' ' : ',';
    out.size = 0;
    out.data = (char**)malloc((size_t)cap * sizeof(char*));
    if (out.data == NULL) return out;

    if (has_space || has_comma) {
        int start = -1;
        for (int i = 0; i <= n; i++) {
            char ch = (i < n) ? txt[i] : sep;
            if (ch == sep) {
                if (start >= 0) {
                    int len = i - start;
                    char* w = (char*)malloc((size_t)len + 1);
                    if (w == NULL) return out;
                    memcpy(w, txt + start, (size_t)len);
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

    {
        int num=0;
        char buf[32];
        for (int i=0;i<n;i++)
            if (txt[i]>=97 && txt[i]<=122 && txt[i]%2==0)
                num+=1;
        sprintf(buf, "%d", num);
        out.size = 1;
        out.data[0] = (char*)malloc(strlen(buf) + 1);
        if (out.data[0] == NULL) {
            out.size = 0;
            return out;
        }
        strcpy(out.data[0], buf);
        return out;
    }
}

