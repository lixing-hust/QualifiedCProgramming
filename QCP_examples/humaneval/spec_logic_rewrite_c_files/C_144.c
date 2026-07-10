/*
Your task is to implement a function that will simplify the expression
x * n. The function returns true if x * n evaluates to a whole number && false
otherwise. Both x && n, are string representation of a fraction, && have the following format,
<numerator>/<denominator> where both numerator && denominator are positive whole numbers.

You can assume that x, && n are valid fractions, && do ! have zero as denominator.

simplify("1/5", "5/1") = true
simplify("1/6", "2/1") = false
simplify("7/10", "10/2") = false
*/
#include<stdio.h>
#include<string.h>
#include<stdbool.h>
bool simplify(const char* x, const char* n){
    int a,b,c,d;
    if (sscanf(x, "%d/%d", &a, &b) != 2) return false;
    if (sscanf(n, "%d/%d", &c, &d) != 2) return false;
    if ((a*c)%(b*d)==0) return true;
    return false;
}

