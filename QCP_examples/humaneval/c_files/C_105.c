/*
Given a vector of integers, sort the integers that are between 1 && 9 inclusive,
reverse the resulting vector, && then replace each digit by its corresponding name from
"One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine".

For example:
  arr = {2, 1, 1, 4, 5, 8, 2, 3}   
        -> sort arr -> {1, 1, 2, 2, 3, 4, 5, 8} 
        -> reverse arr -> {8, 5, 4, 3, 2, 2, 1, 1}
  return {"Eight", "Five", "Four", "Three", "Two", "Two", "One", "One"}

  If the vector is empty, return an empty vector:
  arr = {}
  return {}

  If the vector has any strange number ignore it:
  arr = {1, -1 , 55} 
        -> sort arr -> {-1, 1, 55}
        -> reverse arr -> {55, 1, -1}
  return = {"One"}
*/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

typedef struct {
  const char** data;
  int size;
} StrArray;

static int cmp_int(const void* a, const void* b) {
  int x = *(const int*)a;
  int y = *(const int*)b;
  return (x > y) - (x < y);
}

StrArray by_length(const int* arr, int arr_size){
  static const char* numto[] = {"Zero","One","Two","Three","Four","Five","Six","Seven","Eight","Nine"};
  StrArray out;
  int* tmp = (int*)malloc((size_t)arr_size * sizeof(int));
  out.size = 0;
  out.data = (const char**)malloc((size_t)arr_size * sizeof(const char*));
  if (tmp == NULL || out.data == NULL) {
    free(tmp);
    free(out.data);
    out.data = NULL;
    out.size = 0;
    return out;
  }
  for (int i=0;i<arr_size;i++) tmp[i] = arr[i];
  qsort(tmp, (size_t)arr_size, sizeof(int), cmp_int);
  for (int i=arr_size-1;i>=0;i-=1)
    if (tmp[i]>=1 && tmp[i]<=9)
      out.data[out.size++] = numto[tmp[i]];
  free(tmp);
    return out;
}

