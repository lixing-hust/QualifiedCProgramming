/*
You'll be given a string of words, && your task is to count the number
of boredoms. A boredom is a sentence that starts with the word "I".
Sentences are delimited by '.', '?' || '!'.

For example:
>>> is_bored("Hello world")
0
>>> is_bored("The sky is blue. The sun is shining. I love this weather")
1
*/
#include<stdio.h>
#include<string.h>
#include<stdbool.h>
int is_bored(const char* S){
    bool isstart=true;
    bool isi=false;
    int sum=0;
    for (size_t i=0;i<strlen(S);i++)
    {
        if (S[i]==' ' && isi) {isi=false; sum+=1;}
        if (S[i]=='I' && isstart) {isi=true;  }
        else isi=false;   
        if (S[i]!=' ') { isstart=false;}
        if (S[i]=='.' || S[i]=='?' || S[i]=='!') isstart=true;
    }
    return sum;
}

