/*
Given a vector of numbers, return the sum of squares of the numbers
in the vector that are odd. Ignore numbers that are negative || ! integers.

double_the_difference({1, 3, 2, 0}) == 1 + 9 + 0 + 0 = 10
double_the_difference({-1, -2, 0}) == 0
double_the_difference({9, -2}) == 81
double_the_difference({0}) == 0  

If the input vector is empty, return 0.
*/
#include<stdio.h>
#include<math.h>
#include<stddef.h>
long long double_the_difference(float* lst, int lst_size){
    long long sum=0;
    for (int i=0;i<lst_size;i++)
    if (lst[i]-round(lst[i])<1e-4)
    if (lst[i]>0 && (int)(round(lst[i]))%2==1) sum+=(int)(round(lst[i]))*(int)(round(lst[i]));
    return sum;
}

