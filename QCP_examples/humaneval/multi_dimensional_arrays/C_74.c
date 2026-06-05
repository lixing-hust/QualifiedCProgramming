/*
Write a function that accepts two vectors of strings && returns the vector that has 
total number of chars in the all strings of the vector less than the other vector.

if the two vectors have the same number of chars, return the first vector.

Examples
total_match({}, {}) ➞ {}
total_match({"hi", "admin"}, {"hI", "Hi"}) ➞ {"hI", "Hi"}
total_match({"hi", "admin"}, {"hi", "hi", "admin", "project"}) ➞ {"hi", "admin"}
total_match({"hi", "admin"}, {"hI", "hi", "hi"}) ➞ {"hI", "hi", "hi"}
total_match({"4"}, {"1", "2", "3", "4", "5"}) ➞ {"4"}
*/
#include<stdio.h>
#include<string.h>

typedef struct {
    const char** data;
    int size;
} StrArray;

StrArray total_match(const char** lst1, int lst1_size, const char** lst2, int lst2_size){
    int num1,num2,i;
    StrArray out;
    num1=0;num2=0;
    for (i=0;i<lst1_size;i++)
        num1+=(int)strlen(lst1[i]);
    for (i=0;i<lst2_size;i++)
        num2+=(int)strlen(lst2[i]);
    if (num1>num2) {
        out.data = lst2;
        out.size = lst2_size;
        return out;
    }
    out.data = lst1;
    out.size = lst1_size;
    return out;
}

