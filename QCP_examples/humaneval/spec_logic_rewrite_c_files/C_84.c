/*
Given a positive integer N, return the total sum of its digits in binary.

Example
    For N = 1000, the sum of digits will be 1 the output should be "1".
    For N = 150, the sum of digits will be 6 the output should be "110".
    For N = 147, the sum of digits will be 12 the output should be "1100".

Variables:
    @N integer
         Constraints: 0 ≤ N ≤ 10000.
Output:
     a string of binary number
*/
#include<stdio.h>
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

char* solve(int N){
    int sum=0;
    if (N == 0) {
        return to_binary_string(0);
    }
    while (N > 0) {
        sum += N % 10;
        N /= 10;
    }
    return to_binary_string(sum);
}

