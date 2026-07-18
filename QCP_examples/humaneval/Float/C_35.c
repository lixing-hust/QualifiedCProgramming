/*
Return maximum element in the vector.
>>> max_element({1, 2, 3})
3
>>> max_element({5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10})
123
*/
#include<stdio.h>
#include<math.h>
#include<stddef.h>
float max_element(float* l, int l_size){
  float max=-10000;
  for (int i=0;i<l_size;i++)
  if (max<l[i]) max=l[i];
  return max;

}

