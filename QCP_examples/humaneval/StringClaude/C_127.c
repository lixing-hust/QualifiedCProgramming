/*
You are given two intervals,
where each interval is a pair of integers. For example, interval = (start, end) = (1, 2).
The given intervals are closed which means that the interval (start, end)
includes both start && end.
For each given interval, it is assumed that its start is less || equal its end.
Your task is to determine whether the length of intersection of these two
intervals is a prime number.
Example, the intersection of the intervals (1, 3), (2, 4) is (2, 3)
which its length is 1, which ! a prime number.
If the length of the intersection is a prime number, return "YES",
otherwise, return "NO".
If the two intervals don't intersect, return "NO".


{input/output} samples:
intersection({1, 2}, {2, 3}) ==> "NO"
intersection({-1, 1}, {0, 4}) ==> "NO"
intersection({-3, -1}, {-5, 5}) ==> "YES"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_127_pre_z: list Z -> list Z -> Prop)
               (problem_127_spec_z: list Z -> list Z -> Z -> Prop)
               (interval_int_range: list Z -> Prop)
               (inter_start_z: list Z -> list Z -> Z)
               (inter_end_z: list Z -> list Z -> Z)
               (inter_len_z: list Z -> list Z -> Z)
               (prime_prefix_z: Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_127 */

int intersection(int* interval1, int interval1_size, int* interval2, int interval2_size)
/*@ With i1 i2
    Require
        interval1_size == 2 &&
        interval2_size == 2 &&
        problem_127_pre_z(i1, i2) &&
        interval_int_range(i1) &&
        interval_int_range(i2) &&
        IntArray::full(interval1, interval1_size, i1) *
        IntArray::full(interval2, interval2_size, i2)
    Ensure
        problem_127_spec_z(i1, i2, __return) &&
        IntArray::full(interval1, interval1_size, i1) *
        IntArray::full(interval2, interval2_size, i2)
*/
{
    int s1 = interval1[0];
    int e1 = interval1[1];
    int s2 = interval2[0];
    int e2 = interval2[1];
    int inter1;
    int inter2;

    if (s1 > s2) {
        inter1 = s1;
    } else {
        inter1 = s2;
    }
    if (e1 < e2) {
        inter2 = e1;
    } else {
        inter2 = e2;
    }
    int l = inter2 - inter1;

    /*@ Assert
        interval1 == interval1@pre &&
        interval2 == interval2@pre &&
        interval1_size == interval1_size@pre &&
        interval2_size == interval2_size@pre &&
        interval1_size == 2 &&
        interval2_size == 2 &&
        problem_127_pre_z(i1, i2) &&
        interval_int_range(i1) &&
        interval_int_range(i2) &&
        s1 == Znth(0, i1, 0) &&
        e1 == Znth(1, i1, 0) &&
        s2 == Znth(0, i2, 0) &&
        e2 == Znth(1, i2, 0) &&
        inter1 == inter_start_z(i1, i2) &&
        inter2 == inter_end_z(i1, i2) &&
        l == inter_len_z(i1, i2) &&
        -2000000000 <= l && l <= 2000000000 &&
        IntArray::full(interval1, interval1_size, i1) *
        IntArray::full(interval2, interval2_size, i2)
    */
    if (l < 2) return 0;

    int i;
    /*@ Inv Assert
        interval1 == interval1@pre &&
        interval2 == interval2@pre &&
        interval1_size == interval1_size@pre &&
        interval2_size == interval2_size@pre &&
        interval1_size == 2 &&
        interval2_size == 2 &&
        problem_127_pre_z(i1, i2) &&
        interval_int_range(i1) &&
        interval_int_range(i2) &&
        s1 == Znth(0, i1, 0) &&
        e1 == Znth(1, i1, 0) &&
        s2 == Znth(0, i2, 0) &&
        e2 == Znth(1, i2, 0) &&
        inter1 == inter_start_z(i1, i2) &&
        inter2 == inter_end_z(i1, i2) &&
        l == inter_len_z(i1, i2) &&
        2 <= l && l <= 2000000000 &&
        2 <= i && i <= 46340 &&
        prime_prefix_z(i, l) &&
        IntArray::full(interval1, interval1_size, i1) *
        IntArray::full(interval2, interval2_size, i2)
    */
    for (i = 2; i * i <= l; i++) {
        if (l % i == 0) return 0;
    }
    return 1;
}
