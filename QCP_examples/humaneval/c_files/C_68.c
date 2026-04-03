/*
Given a vector representing a branch of a tree that has non-negative integer nodes
your task is to pluck one of the nodes && return it.
The plucked node should be the node with the smallest even value.
If multiple nodes with the same smallest even value are found return the node that has smallest index.

The plucked node should be returned in a vector, { smalest_value, its index },
If there are no even values || the given vector is empty, return {}.

Example 1:
    Input: {4,2,3}
    Output: {2, 1}
    Explanation: 2 has the smallest even value, && 2 has the smallest index.

Example 2:
    Input: {1,2,3}
    Output: {2, 1}
    Explanation: 2 has the smallest even value, && 2 has the smallest index. 

Example 3:
    Input: {}
    Output: {}

Example 4:
    Input: {5, 0, 3, 0, 4, 2}
    Output: {0, 1}
    Explanation: 0 is the smallest value, but  there are two zeros,
                 so we will choose the first zero, which has the smallest index.

Constraints:
    * 1 <= nodes.length <= 10000
    * 0 <= node.value
*/
#include<stdio.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray pluck(const int* arr, int arr_size){
    IntArray out;
    out.data = NULL;
    out.size = 0;

    for (int i=0;i<arr_size;i++) {
        if (arr[i]%2==0 && (out.size==0 || arr[i]<out.data[0])) {
            if (out.size == 0) {
                out.data = (int*)malloc(2 * sizeof(int));
                if (out.data == NULL) {
                    out.size = 0;
                    return out;
                }
                out.size = 2;
            }
            out.data[0] = arr[i];
            out.data[1] = i;
        }
    }

    return out;
}

