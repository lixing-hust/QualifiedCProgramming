#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<stdbool.h>
bool is_palindrome(const char* str){
    //Test if given string is a palindrome 
    size_t i = 0;
    size_t j = strlen(str);
    if (j == 0) return true;
    j -= 1;
    while (i < j) {
        if (str[i] != str[j]) return false;
        i += 1;
        j -= 1;
    }
    return true;
}
char* make_palindrome(const char* str){
    /*
    Find the shortest palindrome that begins with a supplied string. 
    Algorithm idea is simple: - Find the longest postfix of supplied string that is a palindrome. 
    - Append to the end of the string reverse of a string prefix that comes before the palindromic suffix.
    >>> make_palindrome("") 
    "" 
    >>> make_palindrome("cat") 
    "catac" 
    >>> make_palindrome("cata") 
    "catac" 
    */
   size_t i;
   size_t n = strlen(str);
   char* out;
   for (i=0;i<n;i++)
   {
        if (is_palindrome(str + i))
        {
            size_t add = i;
            out = (char*)malloc(n + add + 1);
            if (out == NULL) return NULL;
            memcpy(out, str, n);
            for (size_t k = 0; k < add; k++) {
                out[n + k] = str[add - 1 - k];
            }
            out[n + add] = '\0';
            return out;
        }
   }
   out = (char*)malloc(2 * n + 1);
   if (out == NULL) return NULL;
   memcpy(out, str, n);
   for (size_t k = 0; k < n; k++) {
       out[n + k] = str[n - 1 - k];
   }
   out[2 * n] = '\0';
   return out;
}

