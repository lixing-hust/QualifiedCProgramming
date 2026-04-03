/*
Task
Write a function that takes a string as input && returns the sum of the upper characters only's
ASCII codes.

Examples:
    digitSum("") => 0
    digitSum("abAB") => 131
    digitSum("abcCd") => 67
    digitSum("helloE") => 69
    digitSum("woArBld") => 131
    digitSum("aAaaaXa") => 153
*/
#include<stdio.h>
#include<string.h>
int digitSum(const char* s){
    int sum=0;
    for (size_t i=0;i<strlen(s);i++)
        if (s[i]>=65 && s[i]<=90)
            sum+=s[i];
    return sum;
}

