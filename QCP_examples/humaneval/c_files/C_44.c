/*
Change numerical base of input number x to base.
return string representation after the conversion.
base numbers are less than 10.
>>> change_base(8, 3)
"22"
>>> change_base(8, 2)
"1000"
>>> change_base(7, 2)
"111"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

char* change_base(int x, int base){
    int digits = 0;
    int t = x;
    char* out;
    if (x == 0) {
        out = (char*)malloc(2);
        if (out != NULL) {
            out[0] = '0';
            out[1] = '\0';
        }
        return out;
    }
    while (t > 0) {
        digits += 1;
        t /= base;
    }
    out = (char*)malloc((size_t)digits + 1);
    if (out == NULL) {
        return NULL;
    }
    out[digits] = '\0';
    while (x > 0) {
        digits -= 1;
        out[digits] = (char)('0' + (x % base));
        x /= base;
    }
    return out;
}

