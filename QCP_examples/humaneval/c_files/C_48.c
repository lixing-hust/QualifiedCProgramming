/*
Checks if given string is a palindrome
>>> is_palindrome("")
true
>>> is_palindrome("aba")
true
>>> is_palindrome("aaaaa")
true
>>> is_palindrome("zbcd")
false
*/
#include<stdio.h>
#include<string.h>
#include<stdbool.h>
bool is_palindrome(const char* text){
    size_t i = 0;
    size_t j = strlen(text);

    if (j == 0) {
        return true;
    }

    j -= 1;
    while (i < j) {
        if (text[i] != text[j]) {
            return false;
        }
        i += 1;
        j -= 1;
    }
    return true;
}

