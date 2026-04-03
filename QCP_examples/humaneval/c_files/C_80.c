/*
You are given a string s.
Your task is to check if the string is happy || !.
A string is happy if its length is at least 3 && every 3 consecutive letters are distinct
For example:
is_happy("a") => false
is_happy("aa") => false
is_happy("abcd") => true
is_happy("aabb") => false
is_happy("adb") => true
is_happy("xyy") => false
*/
#include<stdio.h>
#include<string.h>
#include<stdbool.h>
bool is_happy(const char* s){
    size_t n = strlen(s);
    if (n<3) return false;
    for (size_t i=2;i<n;i++)
    if (s[i]==s[i-1] || s[i]==s[i-2]) return false;
    return true;
}

