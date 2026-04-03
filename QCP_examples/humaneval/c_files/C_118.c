/*
You are given a word. Your task is to find the closest vowel that stands between 
two consonants from the right side of the word (case sensitive).

Vowels in the beginning && ending doesn't count. Return empty string if you didn't
find any vowel met the above condition. 

You may assume that the given string contains English letter only.

Example:
get_closest_vowel("yogurt") ==> "u"
get_closest_vowel("FULL") ==> "U"
get_closest_vowel("quick") ==> ""
get_closest_vowel("ab") ==> ""
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

static int is_vowel(char ch) {
    return strchr("AEIOUaeiou", ch) != NULL;
}

char* get_closest_vowel(const char* word){
    size_t n = strlen(word);
    int i;
    char* out;

    if (n < 3) {
        out = (char*)malloc(1);
        if (out != NULL) {
            out[0] = '\0';
        }
        return out;
    }

    for (i = (int)n - 2; i >= 1; i -= 1) {
        if (is_vowel(word[i]) && !is_vowel(word[i + 1]) && !is_vowel(word[i - 1])) {
            out = (char*)malloc(2);
            if (out == NULL) {
                return NULL;
            }
            out[0] = word[i];
            out[1] = '\0';
            return out;
        }
    }

    out = (char*)malloc(1);
    if (out != NULL) {
        out[0] = '\0';
    }
    return out;
}

