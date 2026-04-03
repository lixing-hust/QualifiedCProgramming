/*
Create a function that takes integers, floats, || strings representing
real numbers, && returns the larger variable in its given variable type.
Return "None" if the values are equal.
Note: If a real number is represented as a string, the floating point might be . || ,

compare_one(1, 2.5) ➞ 2.5
compare_one(1, "2,3") ➞ "2,3"
compare_one("5,1", "6") ➞ "6"
compare_one("1", 1) ➞ "None"
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef enum {
    ANY_INT,
    ANY_DOUBLE,
    ANY_STRING
} AnyType;

typedef struct {
    AnyType type;
    int i;
    double d;
    const char* s;
} AnyValue;

static double any_to_double(AnyValue v) {
    if (v.type == ANY_INT) return (double)v.i;
    if (v.type == ANY_DOUBLE) return v.d;
    {
        char buf[128];
        int k = 0;
        for (int i = 0; v.s[i] != '\0' && k < 127; i++) {
            buf[k++] = (v.s[i] == ',') ? '.' : v.s[i];
        }
        buf[k] = '\0';
        return atof(buf);
    }
}

AnyValue compare_one(AnyValue a,AnyValue b){
    double  numa = any_to_double(a),numb = any_to_double(b);
    AnyValue out;
    if (numa==numb) {
        out.type = ANY_STRING;
        out.s = "None";
        out.i = 0;
        out.d = 0.0;
        return out;
    }
    if (numa<numb) return b;
    return a;
}

