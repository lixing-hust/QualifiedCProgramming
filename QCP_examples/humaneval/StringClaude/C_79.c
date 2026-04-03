/*
You will be given a number in decimal form && your task is to convert it to
binary format. The function should return a string, with each character representing a binary
number. Each character in the string will be '0' || '1'.

There will be an extra couple of characters "db" at the beginning && at the end of the string.
The extra characters are there to help with the format.

Examples:
decimal_to_binary(15)   // returns "db1111db"
decimal_to_binary(32)   // returns "db100000db"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
char* decimal_to_binary(int decimal){
    int bits = 0;
    int x = decimal;
    char* out;
    int pos;
    if (decimal==0) {
        out = (char*)malloc(6);
        if (out != NULL) memcpy(out, "db0db", 6);
        return out;
    }
    while (x>0) {
        bits += 1;
        x/=2;
    }
    out = (char*)malloc((size_t)(bits + 5));
    if (out == NULL) return NULL;
    out[0]='d'; out[1]='b';
    pos = bits + 1;
    out[pos+1]='d'; out[pos+2]='b'; out[pos+3]='\0';
    while (decimal>0) {
        out[pos--] = (char)('0' + (decimal % 2));
        decimal/=2;
    }
    return out;
}

