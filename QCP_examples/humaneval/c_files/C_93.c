/*
Write a function that takes a message, && encodes in such a 
way that it swaps case of all letters, replaces all vowels in 
the message with the letter that appears 2 places ahead of that 
vowel in the english alphabet. 
Assume only letters. 

Examples:
>>> encode('test")
"TGST"
>>> encode("This is a message")
'tHKS KS C MGSSCGG"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
char* encode(const char* message){
    const char* vowels="aeiouAEIOU";
    size_t n = strlen(message);
    char* out = (char*)malloc(n+1);
    if (out == NULL) return NULL;
    for (size_t i=0;i<n;i++)
    {
        char w=message[i];
        if (w>=97 && w<=122){w=w-32;}
        else if (w>=65 && w<=90) w=w+32;
        if (strchr(vowels,w)!=NULL) w=w+2;
        out[i]=w;
    }
    out[n]='\0';
    return out;
}

