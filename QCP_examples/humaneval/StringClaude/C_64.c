/*
Write a function vowels_count which takes a string representing a word as input && returns the number of vowels in the string. Vowels in this case are 'a', 'e', 'i', 'o', 'u'. 
Here, 'y' is also a vowel, but only when it is at the end of the given word.
Example: 
>>> vowels_count("abcde") 
2 
>>> vowels_count("ACEDY") 
3
*/
#include<stdio.h>
#include<string.h>
int vowels_count(const char* s){
    const char* vowels="aeiouAEIOU";
    size_t n = strlen(s);
    int count=0;
    for (size_t i=0;i<n;i++)
    if (strchr(vowels,s[i])!=NULL)
        count+=1;
    if (n>0 && (s[n-1]=='y' || s[n-1]=='Y')) count+=1;
    return count;
}

