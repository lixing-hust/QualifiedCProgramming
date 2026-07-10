/*
Write a function that takes a string && returns an ordered version of it.
Ordered version of string, is a string where all words (separated by space)
are replaced by a new word where all the characters arranged in
ascending order based on ascii value.
Note: You should keep the order of words && blank spaces in the sentence.

For example:
anti_shuffle("Hi") returns "Hi"
anti_shuffle("hello") returns "ehllo"
anti_shuffle("Hello World!!!") returns "Hello !!!Wdlor"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

static int cmp_char(const void* a, const void* b) {
    char x = *(const char*)a;
    char y = *(const char*)b;
    return (x > y) - (x < y);
}

char* anti_shuffle(const char* s){
    int n = (int)strlen(s);
    char* out = (char*)malloc((size_t)n + 1);
    char* cur = (char*)malloc((size_t)n + 1);
    int out_len = 0;
    int cur_len = 0;
    if (out == NULL || cur == NULL) {
        free(out);
        free(cur);
        return NULL;
    }
    for (int i=0;i<=n;i++)
    if (i<n && s[i]!=' ')
    {
        cur[cur_len++] = s[i];
    }
    else
    {
        if (cur_len > 0) {
            qsort(cur, (size_t)cur_len, sizeof(char), cmp_char);
            if (out_len > 0) out[out_len++] = ' ';
            memcpy(out + out_len, cur, (size_t)cur_len);
            out_len += cur_len;
            cur_len = 0;
        }
    }
    out[out_len] = '\0';
    free(cur);
    return out;
}

