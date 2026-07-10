/*
brackets is a string of '(' && ')'.
return true if every opening bracket has a corresponding closing bracket.

>>> correct_bracketing("(")
false
>>> correct_bracketing("()")
true
>>> correct_bracketing("(()())")
true
>>> correct_bracketing(")(()")
false
*/
#include<stdio.h>
#include<string.h>
#include<stdbool.h>
bool correct_bracketing(const char* brackets){
    int level=0;
    for (size_t i=0;i<strlen(brackets);i++)
    {
        if (brackets[i]=='(') level+=1;
        if (brackets[i]==')') level-=1;
        if (level<0) return false;
    }
    if (level!=0) return false;
    return true;
}

