/*
You are given a 2 dimensional data, as a nested vectors,
which is similar to matrix, however, unlike matrices,
each row may contain a different number of columns.
Given lst, && integer x, find integers x in the vector,
&& return vector of vectors, {{x1, y1}, {x2, y2} ...} such that
each vector is a coordinate - {row, columns}, starting with 0.
Sort coordinates initially by rows in ascending order.
Also, sort coordinates of the row by columns in descending order.

Examples:
get_row({
  {1,2,3,4,5,6},
  {1,2,3,4,1,6},
  {1,2,3,4,5,1}
}, 1) == {{0, 0}, {1, 4}, {1, 0}, {2, 5}, {2, 0}}
get_row({}, 1) == {}
get_row({{}, {1}, {1, 2, 3}}, 3) == {{2, 2}}
*/
#include<stdio.h>
#include<stdlib.h>

typedef struct {
  int* data;
  int size;
} IntArray;

IntArray get_row(int** lst, const int* row_sizes, int rows, int x){
  IntArray out;
  int cap = 16;
  out.size = 0;
  out.data = (int*)malloc((size_t)cap * 2 * sizeof(int));
  if (out.data == NULL) return out;
  for (int i=0;i<rows;i++)
  for (int j=row_sizes[i]-1;j>=0;j-=1)
  if (lst[i][j]==x) {
    if (out.size == cap) {
      int new_cap = cap * 2;
      int* tmp = (int*)realloc(out.data, (size_t)new_cap * 2 * sizeof(int));
      if (tmp == NULL) return out;
      out.data = tmp;
      cap = new_cap;
    }
    out.data[out.size * 2] = i;
    out.data[out.size * 2 + 1] = j;
    out.size += 1;
  }
    return out;
}

