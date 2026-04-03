/*
Check if two words have the same characters.
>>> same_chars("eabcdzzzz", "dddzzzzzzzddeddabc")
true
>>> same_chars("abcd", "dddddddabc")
true
>>> same_chars("dddddddabc", "abcd")
true
>>> same_chars("eabcd", "dddddddabc")
false
>>> same_chars("abcd", "dddddddabce")
false
>>> same_chars("eabcdzzzz", "dddzzzzzzzddddabc")
false
*/
#include<stdio.h>
#include<string.h>
#include<stdbool.h>
bool same_chars(const char* s0, const char* s1){
    size_t i;
    for (i = 0; s0[i] != '\0'; i++) {
        if (strchr(s1, s0[i]) == NULL) {
            return false;
        }
    }
    for (i = 0; s1[i] != '\0'; i++) {
        if (strchr(s0, s1[i]) == NULL) {
            return false;
        }
    }
    return true;
}

