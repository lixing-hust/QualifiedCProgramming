/*
Given two vectors operator, && operand. The first vector has basic algebra operations, && 
the second vector is a vector of integers. Use the two given vectors to build the algebric 
expression && return the evaluation of this expression.

The basic algebra operations:
Addition ( + ) 
Subtraction ( - ) 
Multiplication ( * ) 
Floor division ( // ) 
Exponentiation ( ** ) 

Example:
operator{"+", "*", "-"}
vector = {2, 3, 4, 5}
result = 2 + 3 * 4 - 5
=> result = 9

Note:
    The length of operator vector is equal to the length of operand vector minus one.
    Operand is a vector of of non-negative integers.
    Operator vector has at least one operator, && operand vector has at least two operands.

*/
#include<stdio.h>
#include<math.h>
#include<string.h>
#include<stdlib.h>
static int is_in(const char* op, const char* a, const char* b) {
    return strcmp(op, a) == 0 || strcmp(op, b) == 0;
}

int do_algebra(const char** operato, int operato_size, const int* operand, int operand_size){
    int* nums;
    const char** ops;
    int nums_n = operand_size;
    int ops_n = operato_size;

    nums = (int*)malloc((size_t)operand_size * sizeof(int));
    ops = (const char**)malloc((size_t)operato_size * sizeof(const char*));
    if (nums == NULL || ops == NULL) {
        free(nums);
        free(ops);
        return 0;
    }
    for (int i = 0; i < operand_size; i++) nums[i] = operand[i];
    for (int i = 0; i < operato_size; i++) ops[i] = operato[i];

    for (int pass = 0; pass < 3; pass++) {
        int new_nums_n = 0;
        int new_ops_n = 0;
        int* new_nums = (int*)malloc((size_t)nums_n * sizeof(int));
        const char** new_ops = (const char**)malloc((size_t)ops_n * sizeof(const char*));
        if (new_nums == NULL || new_ops == NULL) {
            free(new_nums);
            free(new_ops);
            break;
        }
        new_nums[new_nums_n++] = nums[0];
        for (int i = 0; i < ops_n; i++) {
            int match = 0;
            if (pass == 0) match = strcmp(ops[i], "**") == 0;
            if (pass == 1) match = is_in(ops[i], "*", "//");
            if (pass == 2) match = is_in(ops[i], "+", "-");

            if (match) {
                int left = new_nums[new_nums_n - 1];
                int right = nums[i + 1];
                if (strcmp(ops[i], "**") == 0) new_nums[new_nums_n - 1] = (int)pow(left, right);
                else if (strcmp(ops[i], "*") == 0) new_nums[new_nums_n - 1] = left * right;
                else if (strcmp(ops[i], "//") == 0) new_nums[new_nums_n - 1] = left / right;
                else if (strcmp(ops[i], "+") == 0) new_nums[new_nums_n - 1] = left + right;
                else new_nums[new_nums_n - 1] = left - right;
            } else {
                new_ops[new_ops_n++] = ops[i];
                new_nums[new_nums_n++] = nums[i + 1];
            }
        }
        free(nums);
        free(ops);
        nums = new_nums;
        ops = new_ops;
        nums_n = new_nums_n;
        ops_n = new_ops_n;
    }

    {
        int ans = nums_n > 0 ? nums[0] : 0;
        free(nums);
        free(ops);
        return ans;
    }

}

