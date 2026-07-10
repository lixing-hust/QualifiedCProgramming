/*
In this task, you will be given a string that represents a number of apples && oranges 
that are distributed in a basket of fruit this basket contains 
apples, oranges, && mango fruits. Given the string that represents the total number of 
the oranges && apples && an integer that represent the total number of the fruits 
in the basket return the number of the mango fruits in the basket.
for example:
fruit_distribution("5 apples && 6 oranges", 19) ->19 - 5 - 6 = 8
fruit_distribution("0 apples && 1 oranges",3) -> 3 - 0 - 1 = 2
fruit_distribution("2 apples && 3 oranges", 100) -> 100 - 2 - 3 = 95
fruit_distribution("100 apples && 1 oranges",120) -> 120 - 100 - 1 = 19
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
int fruit_distribution(const char* s, int n){
    int num1 = -1;
    int num2 = -1;
    int cur = -1;

    for (size_t i = 0; i < strlen(s); i++) {
        if (s[i] >= '0' && s[i] <= '9') {
            if (cur < 0) cur = 0;
            cur = cur * 10 + (s[i] - '0');
        } else if (cur >= 0) {
            if (num1 < 0) num1 = cur;
            else if (num2 < 0) num2 = cur;
            cur = -1;
        }
    }

    if (cur >= 0) {
        if (num1 < 0) num1 = cur;
        else if (num2 < 0) num2 = cur;
    }

    if (num1 < 0) num1 = 0;
    if (num2 < 0) num2 = 0;
    return n - num1 - num2;

}

