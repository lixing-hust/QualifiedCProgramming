/*
You are given two positive integers n && m, && your task is to compute the
average of the integers from n through m (including n && m). 
Round the answer to the nearest integer(smaller one) && convert that to binary.
If n is greater than m, return "-1".
Example:
rounded_avg(1, 5) => "11"
rounded_avg(7, 5) => "-1"
rounded_avg(10, 20) => "1111"
rounded_avg(20, 33) => "11010"
*/
#include<stdio.h>
#include<math.h>
#include<stdlib.h>
#include<string.h>

static char* to_binary_string(int num) {
    int bits = 0;
    int x = num;
    char* out;
    if (x == 0) {
        out = (char*)malloc(2);
        if (out != NULL) {
            out[0] = '0';
            out[1] = '\0';
        }
        return out;
    }
    while (x > 0) {
        bits += 1;
        x /= 2;
    }
    out = (char*)malloc((size_t)bits + 1);
    if (out == NULL) {
        return NULL;
    }
    out[bits] = '\0';
    while (num > 0) {
        bits -= 1;
        out[bits] = (char)('0' + (num % 2));
        num /= 2;
    }
    return out;
}

char* rounded_avg(int n, int m){
    int num;
    char* out;
    if (n>m) {
        out = (char*)malloc(3);
        if (out != NULL) {
            out[0] = '-';
            out[1] = '1';
            out[2] = '\0';
        }
        return out;
    }
    num=(m+n)/2;
    return to_binary_string(num);
}

