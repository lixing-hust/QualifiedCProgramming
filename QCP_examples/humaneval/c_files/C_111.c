/*
Given a string representing a space separated lowercase letters, return a map
of the letter with the most repetition && containing the corresponding count.
If several letters have the same occurrence, return all of them.

Example:
histogram("a b c") == {{"a", 1}, {"b", 1}, {"c", 1}}
histogram("a b b a") == {{"a", 2}, {"b", 2}}
histogram("a b c a b") == {{"a", 2}, {"b", 2}}
histogram("b b b b a") == {{"b", 4}}
histogram("") == {}

*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef struct {
    char* keys;
    int* values;
    int size;
} CharIntMap;

CharIntMap histogram(const char* test){
    int count[256] = {0};
    CharIntMap out;
    int max=0;
    out.keys = (char*)malloc(256);
    out.values = (int*)malloc(256 * sizeof(int));
    out.size = 0;
    if (out.keys == NULL || out.values == NULL) {
        free(out.keys);
        free(out.values);
        out.keys = NULL;
        out.values = NULL;
        out.size = 0;
        return out;
    }

    for (int i=0;test[i]!='\0';i++)
        if (test[i]!=' ')
        {
            unsigned char ch = (unsigned char)test[i];
            count[ch]+=1;
            if (count[ch]>max) max=count[ch];
        }

    for (int ch=0; ch<256; ch++) {
        if (count[ch] == max && max > 0) {
            out.keys[out.size] = (char)ch;
            out.values[out.size] = count[ch];
            out.size += 1;
        }
    }
    return out;
}

