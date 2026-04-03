/*
Create a function which takes a string representing a file's name, && returns
"Yes" if the the file's name is valid, && returns "No" otherwise.
A file's name is considered to be valid if && only if all the following conditions 
are met:
- There should ! be more than three digits ('0'-'9') in the file's name.
- The file's name contains exactly one dot "."
- The substring before the dot should ! be empty, && it starts with a letter from 
the latin alphapet ('a'-'z' && 'A'-'Z').
- The substring after the dot should be one of these: {'txt", "exe", "dll"}
Examples:
file_name_check("example.txt") => "Yes"
file_name_check("1example.dll")  => "No" // (the name should start with a latin alphapet letter)
*/
#include<stdio.h>
#include<string.h>
const char* file_name_check(const char* file_name){
    int numdigit=0,numdot=0;
    size_t n = strlen(file_name);
    if (n<5) return "No";
    char w=file_name[0];
    if (w<65 || (w>90 && w<97) || w>122) return "No";
    if (strcmp(file_name + n - 4, ".txt") != 0 && strcmp(file_name + n - 4, ".exe") != 0 && strcmp(file_name + n - 4, ".dll") != 0) return "No";
    for (size_t i=0;i<n;i++)
    {
        if (file_name[i]>=48 && file_name[i]<=57) numdigit+=1;
        if (file_name[i]=='.') numdot+=1;
    }
    if (numdigit>3 || numdot!=1) return "No";
    return "Yes"; 
}

