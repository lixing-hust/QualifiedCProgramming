/*
From a supplied vector of numbers (of length at least two) select && return two that are the closest to each
other && return them in order (smaller number, larger number).
>>> find_closest_elements({1.0, 2.0, 3.0, 4.0, 5.0, 2.2})
(2.0, 2.2)
>>> find_closest_elements({1.0, 2.0, 3.0, 4.0, 5.0, 2.0})
(2.0, 2.0)
*/
#include<stdio.h>
#include<math.h>
#include<stdlib.h>

typedef struct {
    float* data;
    int size;
} FloatArray;

FloatArray find_closest_elements(const float* numbers, int numbers_size){
    FloatArray out;
    out.data = (float*)malloc(2 * sizeof(float));
    out.size = 2;

    if (out.data == NULL) {
        out.size = 0;
        return out;
    }

    out.data[0] = numbers[0];
    out.data[1] = numbers[1];
    for (int i=0;i<numbers_size;i++)
    for (int j=i+1;j<numbers_size;j++)
        if (fabsf(numbers[i]-numbers[j]) < fabsf(out.data[0]-out.data[1])) {
            out.data[0] = numbers[i];
            out.data[1] = numbers[j];
        }
    if (out.data[0] > out.data[1]) {
        float t = out.data[0];
        out.data[0] = out.data[1];
        out.data[1] = t;
    }
    return out;
}

