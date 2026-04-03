/*
You are given a string s.
if s[i] is a letter, reverse its case from lower to upper || vise versa, 
otherwise keep it as it is.
If the string contains no letters, reverse the string.
The function should return the resulted string.
Examples
solve("1234") = "4321"
solve("ab") = "AB"
solve("#a@C") = "#A@c"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
char* solve(const char* s){
    size_t n = strlen(s);
    int nletter=0;
    char* out=(char*)malloc(n+1);
    if (out == NULL) return NULL;
    for (size_t i=0;i<n;i++)
    {
        char w=s[i];
        if (w>=65 && w<=90) w=w+32;
        else if (w>=97 && w<=122) w=w-32;
        else nletter+=1;
        out[i]=w;
    }
    out[n]='\0';
    if (nletter==(int)n)
    {
        char* p=(char*)malloc(n+1);
        if (p == NULL) {
            free(out);
            return NULL;
        }
        for (size_t i=0;i<n;i++) p[i]=s[n-1-i];
        p[n]='\0';
        free(out);
        return p;
    }
    else return out;
}

