/*
Input is a space-delimited string of numberals from "zero" to "nine".
Valid choices are "zero", "one", 'two", 'three", "four", "five", 'six", 'seven", "eight" && "nine".
Return the string with numbers sorted from smallest to largest
>>> sort_numbers('three one five")
"one three five"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

char* sort_numbers(const char* numbers){
    const char* words[] = {"zero","one","two","three","four","five","six","seven","eight","nine"};
    int count[10];
    int n = (int)strlen(numbers);
    char token[32];
    int tlen = 0;
    int out_len = 1;
    char* out;

    for (int i=0;i<10;i++) count[i]=0;
    for (int i=0;i<=n;i++) {
        char ch = (i < n) ? numbers[i] : ' ';
        if (ch == ' ') {
            if (tlen > 0) {
                token[tlen] = '\0';
                for (int d=0; d<10; d++) {
                    if (strcmp(token, words[d]) == 0) {
                        count[d] += 1;
                        break;
                    }
                }
                tlen = 0;
            }
        } else if (tlen < 31) {
            token[tlen++] = ch;
        }
    }
    for (int i=0;i<10;i++)
        out_len += count[i] * ((int)strlen(words[i]) + 1);

    out = (char*)malloc((size_t)out_len);
    if (out == NULL) return NULL;
    out[0] = '\0';
    {
        int first = 1;
        for (int i=0;i<10;i++)
            for (int j=0;j<count[i];j++) {
                if (!first) strcat(out, " ");
                strcat(out, words[i]);
                first = 0;
            }
    }
    return out;
}

