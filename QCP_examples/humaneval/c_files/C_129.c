/*
Given a grid with N rows && N columns (N >= 2) && a positive integer k, 
each cell of the grid contains a value. Every integer in the range {1, N * N}
inclusive appears exactly once on the cells of the grid.

You have to find the minimum path of length k in the grid. You can start
from any cell, && in each step you can move to any of the neighbor cells,
in other words, you can go to cells which share an edge with you current
cell.
Please note that a path of length k means visiting exactly k cells (!
necessarily distinct).
You CANNOT go off the grid.
A path A (of length k) is considered less than a path B (of length k) if
after making the ordered vectors of the values on the cells that A && B go
through (let's call them lst_A && lst_B), lst_A is lexicographically less
than lst_B, in other words, there exist an integer index i (1 <= i <= k)
such that lst_A[i] < lst_B[i] && for any j (1 <= j < i) we have
lst_A[j] = lst_B[j].
It is guaranteed that the answer is unique.
Return an ordered vector of the values on the cells that the minimum path go through.

Examples:

    Input: grid = { {1,2,3}, {4,5,6}, {7,8,9}}, k = 3
    Output: {1, 2, 1}

    Input: grid = { {5,9,3}, {4,1,6}, {7,8,2}}, k = 1
    Output: {1}
*/
#include<stdio.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray minPath(int** grid, int n, int k){
    int i,j,x,y,min;
    IntArray out;
    out.size = k;
    out.data = (int*)malloc((size_t)k * sizeof(int));
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }

    for (i=0;i<n;i++)
        for (j=0;j<n;j++)
            if (grid[i][j]==1) {
                x=i;y=j;
            }
    min=n*n;
    if (x>0 && grid[x-1][y]<min) min=grid[x-1][y];
    if (x<n-1 && grid[x+1][y]<min) min=grid[x+1][y];
    if (y>0 && grid[x][y-1]<min) min=grid[x][y-1];
    if (y<n-1 && grid[x][y+1]<min) min=grid[x][y+1];
    for (i=0;i<k;i++)
    if (i%2==0) out.data[i] = 1;
    else out.data[i] = min;
    return out;
}

