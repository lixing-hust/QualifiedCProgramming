/*
Create a function that returns true if the last character
of a given string is an alphabetical character && is !
a part of a word, && false otherwise.
Note: "word" is a group of characters separated by space.

Examples:
check_if_last_char_is_a_letter("apple pie") ➞ false
check_if_last_char_is_a_letter("apple pi e") ➞ true
check_if_last_char_is_a_letter("apple pi e ") ➞ false
check_if_last_char_is_a_letter("") ➞ false 
*/
#include<stdio.h>
#include<string.h>
#include<stdbool.h>
bool check_if_last_char_is_a_letter(const char* txt){
    size_t n = strlen(txt);
    if (n==0) return false;
    char chr=txt[n-1];
    if (chr<65 || (chr>90 && chr<97) || chr>122) return false;
    if (n==1) return true;
    chr=txt[n-2];
    if ((chr>=65 && chr<=90) || (chr>=97 && chr<=122)) return false;
    return true;
}

