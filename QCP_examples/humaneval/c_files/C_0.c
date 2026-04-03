/*
Check if in given vector of numbers, are any two numbers closer to each other than
given threshold.
>>> has_close_elements({1.0, 2.0, 3.0}, 0.5)
false
>>> has_close_elements({1.0, 2.8, 3.0, 4.0, 5.0, 2.0}, 0.3)
true
*/
#include<stdio.h>
#include<stddef.h>
#include<math.h>
#include<stdbool.h>
bool has_close_elements(float* numbers, int numbers_size, float threshold){
    int i,j;
    
    for (i=0;i<numbers_size;i++)
    for (j=i+1;j<numbers_size;j++)
    if (abs(numbers[i]-numbers[j])<threshold)
    return true;

    return false;
}


