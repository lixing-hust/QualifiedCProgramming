/*
You are given a vector of two strings, both strings consist of open
parentheses '(' || close parentheses ')' only.
Your job is to check if it is possible to concatenate the two strings in
some order, that the resulting string will be good.
A string S is considered to be good if && only if all parentheses in S
are balanced. For example: the string "(())()" is good, while the string
"())" is !.
Return "Yes" if there's a way to make a good string, && return "No" otherwise.

Examples:
match_parens({"()(", ")"}) == "Yes"
match_parens({")", ")"}) == "No"
*/
#include<stdio.h>
#include<string.h>
#include<stdbool.h>
const char* match_parens(const char* s1, const char* s2){
    int i,count=0;
    bool can=true;
    for (i=0;s1[i]!='\0';i++)
        {
            if (s1[i]=='(') count+=1;
            if (s1[i]==')') count-=1;
            if (count<0) can=false;
        }
    for (i=0;s2[i]!='\0';i++)
        {
            if (s2[i]=='(') count+=1;
            if (s2[i]==')') count-=1;
            if (count<0) can=false;
        }
    if (count!=0) return "No";
    if (can==true) return "Yes";
    count=0;
    can=true;
    for (i=0;s2[i]!='\0';i++)
        {
            if (s2[i]=='(') count+=1;
            if (s2[i]==')') count-=1;
            if (count<0) can=false;
        }
    for (i=0;s1[i]!='\0';i++)
        {
            if (s1[i]=='(') count+=1;
            if (s1[i]==')') count-=1;
            if (count<0) can=false;
        }
    if (can==true) return "Yes";
    return "No";
}

