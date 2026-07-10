/*
You are given 2 words. You need to return true if the second word || any of its rotations is a substring in the first word
cycpattern_check("abcd","abd") => false
cycpattern_check("hello","ell") => true
cycpattern_check("whassup","psus") => false
cycpattern_check("abab","baa") => true
cycpattern_check("efef","eeff") => false
cycpattern_check("himenss",'simen") => true

*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<stdbool.h>
bool cycpattern_check(const char* a, const char* b){
    int n = (int)strlen(b);
    char* rotate = (char*)malloc((size_t)n + 1);
    if (rotate == NULL) return false;
    for (int i=0;i<n;i++)
    {
        for (int j = 0; j < n; j++) rotate[j] = b[(i + j) % n];
        rotate[n] = '\0';
        if (strstr(a, rotate) != NULL) {
            free(rotate);
            return true;
        }
    }
    free(rotate);
    return false;

}

