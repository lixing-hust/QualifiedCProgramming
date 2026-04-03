/*
In this problem, you will implement a function that takes two vectors of numbers,
&& determines whether it is possible to perform an exchange of elements
between them to make lst1 a vector of only even numbers.
There is no limit on the number of exchanged elements between lst1 && lst2.
If it is possible to exchange elements between the lst1 && lst2 to make
all the elements of lst1 to be even, return "YES".
Otherwise, return "NO".
For example:
exchange({1, 2, 3, 4}, {1, 2, 3, 4}) => "YES"
exchange({1, 2, 3, 4}, {1, 5, 3, 4}) => "NO"
It is assumed that the input vectors will be non-empty.
*/
#include<stdio.h>
#include<stddef.h>
#include<string.h>
const char* exchange(int* lst1, int lst1_size, int* lst2, int lst2_size){
    int num=0;
    for (int i=0;i<lst1_size;i++)
    if (lst1[i]%2==0) num+=1;
    for (int i=0;i<lst2_size;i++)
    if (lst2[i]%2==0) num+=1;
    if (num>=lst1_size) return "YES";
    return "NO";
}

