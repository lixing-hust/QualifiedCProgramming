/*
Given a string s && a natural number n, you have been tasked to implement 
a function that returns a vector of all words from string s that contain exactly 
n consonants, in order these words appear in the string s.
If the string s is empty then the function should return an empty vector.
Note: you may assume the input string contains only letters && spaces.
Examples:
select_words("Mary had a little lamb", 4) ==> {"little"}
select_words("Mary had a little lamb", 3) ==> {"Mary", "lamb"}
select_words('simple white space", 2) ==> {}
select_words("Hello world", 4) ==> {"world"}
select_words("Uncle sam", 3) ==> {"Uncle"}
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef struct {
    char** data;
    int size;
} StrArray;

StrArray select_words(const char* s,int n){
    const char* vowels="aeiouAEIOU";
    int len = (int)strlen(s);
    int cap = 8;
    int start = -1;
    StrArray out;
    int numc=0;
    out.size = 0;
    out.data = (char**)malloc((size_t)cap * sizeof(char*));
    if (out.data == NULL) return out;
    for (int i=0;i<=len;i++)
        if (i==len || s[i]==' ')
        {
            if (start >= 0 && numc==n) {
                int wlen = i - start;
                char* w = (char*)malloc((size_t)wlen + 1);
                if (w == NULL) return out;
                memcpy(w, s + start, (size_t)wlen);
                w[wlen] = '\0';
                if (out.size == cap) {
                    int new_cap = cap * 2;
                    char** tmp = (char**)realloc(out.data, (size_t)new_cap * sizeof(char*));
                    if (tmp == NULL) return out;
                    out.data = tmp;
                    cap = new_cap;
                }
                out.data[out.size++] = w;
            }
            start = -1;
            numc=0;
        }
        else
        {
            if (start < 0) start = i;
            if ((s[i]>=65 && s[i]<=90) || (s[i]>=97 && s[i]<=122))
            if (strchr(vowels,s[i])==NULL)
                numc+=1;
        }
    return out;
}

