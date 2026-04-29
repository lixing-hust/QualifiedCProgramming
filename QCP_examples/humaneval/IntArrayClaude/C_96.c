/*
Implement a function that takes an non-negative integer && returns a vector of the first n
integers that are prime numbers && less than n.
for example:
count_up_to(5) => {2,3}
count_up_to(11) => {2,3,5,7}
count_up_to(0) => {}
count_up_to(20) => {2,3,5,7,11,13,17,19}
count_up_to(1) => {}
count_up_to(18) => {2,3,5,7,11,13,17}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_96_pre_z: Z -> Prop)
               (problem_96_spec_z: Z -> list Z -> Prop)
               (count_up_to_state: Z -> list Z -> Prop)
               (prime_test_state: Z -> list Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_96 */

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/;

int *malloc_int_array(int size)
/*@ Require size >= 0 && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

IntArray *count_up_to(int n)
/*@ Require
        0 <= n && n < INT_MAX &&
        problem_96_pre_z(n)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        output_size == Zlength(output_l) &&
        0 <= output_size && output_size <= n &&
        problem_96_spec_z(n, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, n)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->data = malloc_int_array(n);
    int *data = out->data;
    int output_size = 0;
    out->size = 0;
    int i;

    if (n > 2) {
        /*@ Inv Assert
            exists output_l,
            out != 0 &&
            data != 0 &&
            n == n@pre &&
            2 < n && n < INT_MAX &&
            2 <= i && i <= n &&
            0 <= output_size && output_size == Zlength(output_l) &&
            output_size <= n &&
            (output_size == 0 || output_size < i) &&
            count_up_to_state(i, output_l) &&
            data_at(&(out->data), data) *
            data_at(&(out->size), 0) *
            IntArray::seg(data, 0, output_size, output_l) *
            IntArray::undef_seg(data, output_size, n)
        */
        for (i=2;i<n;i++)
        {
            if (output_size == 0) {
                /*@ Assert
                    exists output_l,
                    out != 0 &&
                    data != 0 &&
                    n == n@pre &&
                    2 < n && n < INT_MAX &&
                    2 <= i && i < n &&
                    output_size == 0 &&
                    output_size == Zlength(output_l) &&
                    output_l == nil &&
                    count_up_to_state(i, output_l) &&
                    data_at(&(out->data), data) *
                    data_at(&(out->size), 0) *
                    IntArray::seg(data, 0, output_size, output_l) *
                    IntArray::undef_seg(data, output_size, n)
                */
                data[output_size] = i;
                output_size = output_size + 1;
            } else {
                int j;
                int isp=1;
                /*@ Inv Assert
                    exists output_l,
                    out != 0 &&
                    data != 0 &&
                    n == n@pre &&
                    2 < n && n < INT_MAX &&
                    0 <= output_size && output_size == Zlength(output_l) &&
                    output_size <= n &&
                    output_size < i &&
                    2 <= i && i < n &&
                    0 <= j && j <= output_size &&
                    0 <= isp && isp <= 1 &&
                    count_up_to_state(i, output_l) &&
                    prime_test_state(i, output_l, j, isp) &&
                    data_at(&(out->data), data) *
                    data_at(&(out->size), 0) *
                    IntArray::seg(data, 0, output_size, output_l) *
                    IntArray::undef_seg(data, output_size, n)
                */
                for (j=0;j<output_size && data[j] <= i/data[j];j++) {
                    /*@ Assert
                        exists output_l,
                        out != 0 &&
                        data != 0 &&
                        n == n@pre &&
                        2 < n && n < INT_MAX &&
                        0 <= output_size && output_size == Zlength(output_l) &&
                        output_size <= n &&
                        output_size < i &&
                        2 <= i && i < n &&
                        0 <= j && j < output_size &&
                        0 <= isp && isp <= 1 &&
                        Znth(j, output_l, 0) <= i / Znth(j, output_l, 0) &&
                        count_up_to_state(i, output_l) &&
                        prime_test_state(i, output_l, j, isp) &&
                        data_at(&(out->data), data) *
                        data_at(&(out->size), 0) *
                        IntArray::seg(data, 0, output_size, output_l) *
                        IntArray::undef_seg(data, output_size, n)
                    */
                    if (i%data[j]==0) isp=0;
                }
                if (isp) {data[output_size] = i; output_size = output_size + 1;}
            }
        }
    }
    out->size = output_size;
    return out;
}
