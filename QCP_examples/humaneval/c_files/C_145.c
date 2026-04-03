/*
Write a function which sorts the given vector of integers
in ascending order according to the sum of their digits.
Note: if there are several items with similar sum of their digits,
order them based on their index in original vector.

For example:
>>> order_by_points({1, 11, -1, -11, -12}) == {-1, -11, 1, -12, 11}
>>> order_by_points({}) == {}
*/
#include<stdio.h>
#include<math.h>
#include<string.h>
#include<stdlib.h>

typedef struct {
    int* data;
    int size;
} IntArray;

static int signed_digit_score(int x) {
    int t = abs(x);
    int msd;
    int sum = 0;
    while (t >= 10) t /= 10;
    msd = t;
    sum += (x >= 0) ? msd : -msd;
    t = abs(x);
    if (t >= 10) {
        int p = 1;
        while (p * 10 <= t) p *= 10;
        t %= p;
    } else t = 0;
    while (t > 0) {
        sum += t % 10;
        t /= 10;
    }
    return sum;
}

IntArray order_by_points(const int* nums, int nums_size){
    IntArray out;
    int* score;
    out.size = nums_size;
    out.data = (int*)malloc((size_t)nums_size * sizeof(int));
    score = (int*)malloc((size_t)nums_size * sizeof(int));
    if (out.data == NULL || score == NULL) {
        free(out.data);
        free(score);
        out.size = 0;
        out.data = NULL;
        return out;
    }
    for (int i=0;i<nums_size;i++) {
        out.data[i] = nums[i];
        score[i] = signed_digit_score(nums[i]);
    }
    for (int i=0;i<nums_size;i++)
    for (int j=1;j<nums_size;j++)
    if (score[j-1]>score[j])
    {
        int m=score[j];score[j]=score[j-1];score[j-1]=m;
        m=out.data[j];out.data[j]=out.data[j-1];out.data[j-1]=m;
    }
    free(score);
    return out;
}

