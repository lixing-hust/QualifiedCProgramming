/*
Given a string text, replace all spaces in it with underscores, 
&& if a string has more than 2 consecutive spaces, 
then replace all consecutive spaces with - 

fix_spaces("Example") == "Example"
fix_spaces("Example 1") == "Example_1"
fix_spaces(" Example 2") == "_Example_2"
fix_spaces(" Example   3") == "_Example-3"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
char* fix_spaces(const char* text){
    size_t n = strlen(text);
    char* out = (char*)malloc(n + 1);
    size_t k = 0;
    int spacelen=0;
    if (out == NULL) return NULL;
    for (size_t i=0;i<n;i++)
    if (text[i]==' ') spacelen+=1;
    else
    {
        if (spacelen==1) out[k++] = '_';
        if (spacelen==2) {out[k++] = '_'; out[k++] = '_';}
        if (spacelen>2) out[k++] = '-';
        spacelen=0;
        out[k++] = text[i];
    }
    if (spacelen==1) out[k++] = '_';
    if (spacelen==2) {out[k++] = '_'; out[k++] = '_';}
    if (spacelen>2) out[k++] = '-';
    out[k] = '\0';
    return out;
}

