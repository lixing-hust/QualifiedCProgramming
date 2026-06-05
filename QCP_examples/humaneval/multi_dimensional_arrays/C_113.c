/*
Given a vector of strings, where each string consists of only digits, return a vector.
Each element i of the output should be 'the number of odd elements in the
string i of the input." where all the i's should be replaced by the number
of odd digits in the i'th string of the input.

>>> odd_count({"1234567"})
{'the number of odd elements 4n the str4ng 4 of the 4nput."}
>>> odd_count({"3","11111111"})
{'the number of odd elements 1n the str1ng 1 of the 1nput.",
 'the number of odd elements 8n the str8ng 8 of the 8nput."}
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef struct {
    char** data;
    int size;
} StrArray;

StrArray odd_count(char** lst, int lst_size){
    StrArray out;
    const char* tpl = "the number of odd elements in the string i of the input.";
    out.size = lst_size;
    out.data = (char**)malloc((size_t)lst_size * sizeof(char*));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }
    for (int i=0;i<lst_size;i++)
        {
            int sum=0;
            char numbuf[32];
            int k = 0;
            int numlen;
            int outlen = 0;
            for (size_t j=0;j<strlen(lst[i]);j++)
                if (lst[i][j]>=48 && lst[i][j]<=57 && lst[i][j]%2==1)
                sum+=1;
            sprintf(numbuf, "%d", sum);
            numlen = (int)strlen(numbuf);
            for (size_t j=0;j<strlen(tpl);j++) {
                if (tpl[j]=='i') outlen += numlen;
                else outlen += 1;
            }
            out.data[i] = (char*)malloc((size_t)outlen + 1);
            if (out.data[i] == NULL) return out;
            for (size_t j=0;j<strlen(tpl);j++) {
                if (tpl[j]=='i') {
                    memcpy(out.data[i] + k, numbuf, (size_t)numlen);
                    k += numlen;
                } else {
                    out.data[i][k++] = tpl[j];
                }
            }
            out.data[i][k] = '\0';
        }
    return out;
}

