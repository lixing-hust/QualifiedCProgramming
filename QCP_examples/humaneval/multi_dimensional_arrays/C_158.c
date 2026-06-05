/*
Write a function that accepts a vector of strings.
The vector contains different words. Return the word with maximum number
of unique characters. If multiple strings have maximum number of unique
characters, return the one which comes first in lexicographical order.

find_max({"name", "of", 'string"}) == 'string"
find_max({"name", "enam", "game"}) == "enam"
find_max({"aaaaaaa", "bb" ,"cc"}) == "aaaaaaa"
*/
#include<stdio.h>
#include<string.h>

const char* find_max(char** words, int words_size){
    const char* max="";
    int maxu=0;
    for (int i=0;i<words_size;i++)
    {
        int seen[256] = {0};
        int unique = 0;
        for (size_t j=0;j<strlen(words[i]);j++)
            if (!seen[(unsigned char)words[i][j]]) {
                seen[(unsigned char)words[i][j]] = 1;
                unique += 1;
            }
        if (unique>maxu || (unique==maxu && strcmp(words[i], max) < 0))
        {
            max=words[i];
            maxu=unique;
        }
    }
    return max;
}

