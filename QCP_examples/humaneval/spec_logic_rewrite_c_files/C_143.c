/*
You are given a string representing a sentence,
the sentence contains some words separated by a space,
&& you have to return a string that contains the words from the original sentence,
whose lengths are prime numbers,
the order of the words in the new string should be the same as the original one.

Example 1:
    Input: sentence = "This is a test"
    Output: "is"

Example 2:
    Input: sentence = "lets go for swimming"
    Output: "go for"

Constraints:
    * 1 <= len(sentence) <= 100
    * sentence contains only letters
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<stdbool.h>
char* words_in_sentence(const char* sentence){
    int n = (int)strlen(sentence);
    char* out = (char*)malloc((size_t)n + 1);
    int out_len = 0;
    int start = -1;
    if (out == NULL) return NULL;

    for (int i=0;i<=n;i++)
    if (i<n && sentence[i]!=' ') {
        if (start < 0) start = i;
    } else {
        if (start >= 0) {
            bool isp=true;
            int l=i-start;
            if (l<2) isp=false;
            for (int j=2;j*j<=l;j++)
                if (l%j==0) isp=false;
            if (isp) {
                if (out_len > 0) out[out_len++] = ' ';
                memcpy(out + out_len, sentence + start, (size_t)l);
                out_len += l;
            }
            start = -1;
        }
    }
    out[out_len] = '\0';
    return out;
}

