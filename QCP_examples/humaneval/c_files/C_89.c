/*
Create a function encrypt that takes a string as an argument &&
returns a string encrypted with the alphabet being rotated. 
The alphabet should be rotated in a manner such that the letters 
shift down by two multiplied to two places.
For example:
encrypt("hi") returns "lm"
encrypt("asdfghjkl") returns "ewhjklnop"
encrypt("gf") returns "kj"
encrypt("et") returns "ix"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
char* encrypt(const char* s){
    size_t i;
    size_t n = strlen(s);
    char* out = (char*)malloc(n + 1);
    if (out == NULL) {
        return NULL;
    }
    for (i=0;i<n;i++)
    {
        int w=((int)s[i]+4-(int)'a')%26+(int)'a';
        out[i]=(char)w;
    }
    out[n]='\0';
    return out;
}

