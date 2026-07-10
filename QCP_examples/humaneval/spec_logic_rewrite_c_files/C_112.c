/*
Task
We are given two strings s && c, you have to deleted all the characters in s that are equal to any character in c
then check if the result string is palindrome.
A string is called palindrome if it reads the same backward as forward.
You should return a vector containing the result string && "True"/"False" for the check.
Example
For s = "abcde", c = "ae", the result should be ("bcd","False")
For s = "abcdef", c = "b"  the result should be ("acdef","False")
For s = "abcdedcba", c = "ab", the result should be ("cdedc","True")
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef struct {
    char** data;
    int size;
} StrArray;

StrArray reverse_delete(const char* s,const char* c){
    StrArray out;
    int n = (int)strlen(s);
    int k = 0;
    char* filtered = (char*)malloc((size_t)n + 1);
    int pal = 1;
    out.size = 2;
    out.data = (char**)malloc(2 * sizeof(char*));
    if (filtered == NULL || out.data == NULL) {
        free(filtered);
        free(out.data);
        out.size = 0;
        out.data = NULL;
        return out;
    }

    for (int i=0;i<n;i++) {
        if (strchr(c, s[i]) == NULL) {
            filtered[k++] = s[i];
        }
    }
    filtered[k] = '\0';

    for (int i=0;i<k/2;i++) {
        if (filtered[i] != filtered[k-1-i]) {
            pal = 0;
            break;
        }
    }

    out.data[0] = filtered;
    out.data[1] = (char*)malloc(pal ? 5 : 6);
    if (out.data[1] == NULL) {
        free(filtered);
        free(out.data);
        out.size = 0;
        out.data = NULL;
        return out;
    }
    if (pal) memcpy(out.data[1], "True", 5);
    else memcpy(out.data[1], "False", 6);
    return out;
}

