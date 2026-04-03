/*
Given a positive integer, obtain its roman numeral equivalent as a string,
&& return it in lowercase.
Restrictions: 1 <= num <= 1000

Examples:
>>> int_to_mini_roman(19) == "xix"
>>> int_to_mini_roman(152) == "clii"
>>> int_to_mini_roman(426) == "cdxxvi"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
char* int_to_mini_romank(int number){
    const char* rep[] = {"m","cm","d","cd","c","xc","l","xl","x","ix","v","iv","i"};
    const int num[] = {1000,900,500,400,100,90,50,40,10,9,5,4,1};
    char* current = (char*)malloc(64);
    int cur_len = 0;
    int pos=0;
    if (current == NULL) return NULL;
    current[0] = '\0';
    while(number>0)
    {
        while (number>=num[pos])
        {
            int add = (int)strlen(rep[pos]);
            memcpy(current + cur_len, rep[pos], (size_t)add);
            cur_len += add;
            current[cur_len] = '\0';
            number-=num[pos];
        }
        if (number>0) pos+=1;
    }
    return current;
}

