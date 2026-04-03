/*
Find how many times a given substring can be found in the original string. Count overlaping cases.
>>> how_many_times("", "a")
0
>>> how_many_times("aaa", "a")
3
>>> how_many_times("aaaa", "aa")
3
*/
#include<stdio.h>
#include<string.h>
int how_many_times(const char* str, const char* substring){
    int out=0;
    size_t n = strlen(str);
    size_t m = strlen(substring);
    if (n==0 || m==0 || m>n) return 0;
    for (size_t i=0;i<=n-m;i++)
    if (memcmp(str + i, substring, m)==0)
        out+=1;
    return out;
}

