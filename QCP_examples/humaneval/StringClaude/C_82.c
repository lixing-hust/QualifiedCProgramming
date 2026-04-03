/*
Write a function that takes a string && returns true if the string
length is a prime number || false otherwise
Examples
prime_length("Hello") == true
prime_length("abcdcba") == true
prime_length("kittens") == true
prime_length("orange") == false
*/
#include<stdio.h>
#include<string.h>
#include<stdbool.h>
bool prime_length(const char* str){
    int l,i;
    l=(int)strlen(str);
    if (l<2) return false;
    for (i=2;i*i<=l;i++)
    if (l%i==0) return false;
    return true;
}

