/*
Input to this function is a string representing musical notes in a special ASCII format.
Your task is to parse this string && return vector of integers corresponding to how many beats does each
! last.

Here is a legend:
"o" - whole note, lasts four beats
"o|" - half note, lasts two beats
".|" - quater note, lasts one beat

>>> parse_music("o o| .| o| o| .| .| .| .| o o")
{4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_17_pre_z: list Z -> Prop)
               (problem_17_spec_z: list Z -> list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (music_prefix_output_z: Z -> list Z -> list Z)
               (music_prefix_state_z: Z -> list Z -> Z)
               (music_step_output_z: list Z -> Z -> Z -> list Z)
               (music_step_state_z: Z -> Z -> Z)
               (music_final_output_z: list Z -> Z -> list Z) */
/*@ Import Coq Require Import coins_17 */

typedef struct {
    int *data;
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

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

IntArray *parse_music(char *music_string)
/*@ With l len orig
    Require
        music_string == orig &&
        0 <= len && len + 1 < INT_MAX &&
        Zlength(l) == len &&
        problem_17_pre_z(l) &&
        ascii_range_z(l) &&
        CharArray::full(music_string, len + 1, app(l, cons(0, nil)))
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        output_size == Zlength(output_l) &&
        0 <= output_size && output_size <= len + 1 &&
        problem_17_spec_z(l, output_l) &&
        CharArray::full(orig, len + 1, app(l, cons(0, nil))) *
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, len + 1)
*/
{
    IntArray *out = malloc_int_array_struct();
    int n = strlen(music_string) /*@ where l = l, n = len */;
    out->size = 0;
    out->data = malloc_int_array(n + 1);
    int *data = out->data;
    int state = 0;
    int i;

    /*@ Inv Assert
        exists output_l output_size,
        out != 0 &&
        data != 0 &&
        music_string == orig &&
        n == len &&
        0 <= len && len + 1 < INT_MAX &&
        Zlength(l) == len &&
        problem_17_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= n &&
        0 <= state && state <= 5 &&
        output_size == Zlength(output_l) &&
        0 <= output_size && output_size <= i &&
        output_l == music_prefix_output_z(i, l) &&
        state == music_prefix_state_z(i, l) &&
        CharArray::full(music_string, len + 1, app(l, cons(0, nil))) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), output_size) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, len + 1)
    */
    for (i = 0; i < n; i++) {
        if (music_string[i] == 32) {
            if (state == 1) {
                data[out->size] = 4;
                out->size = out->size + 1;
            } else if (state == 2) {
                data[out->size] = 2;
                out->size = out->size + 1;
            } else if (state == 4) {
                data[out->size] = 1;
                out->size = out->size + 1;
            }
            state = 0;
        } else {
            if (state == 0 && music_string[i] == 111) {
                state = 1;
            } else if (state == 0 && music_string[i] == 46) {
                state = 3;
            } else if (state == 1 && music_string[i] == 124) {
                state = 2;
            } else if (state == 3 && music_string[i] == 124) {
                state = 4;
            } else {
                state = 5;
            }
        }
        /*@ Assert
            exists output_l output_size,
            out != 0 &&
            data != 0 &&
            music_string == orig &&
            n == len &&
            0 <= len && len + 1 < INT_MAX &&
            Zlength(l) == len &&
            problem_17_pre_z(l) &&
            ascii_range_z(l) &&
            0 <= i && i < n &&
            0 <= state && state <= 5 &&
            output_size == Zlength(output_l) &&
            0 <= output_size && output_size <= i + 1 &&
            output_l == music_prefix_output_z(i + 1, l) &&
            state == music_prefix_state_z(i + 1, l) &&
            CharArray::full(music_string, len + 1, app(l, cons(0, nil))) *
            data_at(&(out -> data), data) *
            data_at(&(out -> size), output_size) *
            IntArray::seg(data, 0, output_size, output_l) *
            IntArray::undef_seg(data, output_size, len + 1)
        */
    }

    if (state == 1) {
        data[out->size] = 4;
        out->size = out->size + 1;
    } else if (state == 2) {
        data[out->size] = 2;
        out->size = out->size + 1;
    } else if (state == 4) {
        data[out->size] = 1;
        out->size = out->size + 1;
    }

    /*@ Assert
        exists output_l output_size,
        out != 0 &&
        data != 0 &&
        music_string == orig &&
        n == len &&
        i == len &&
        0 <= len && len + 1 < INT_MAX &&
        Zlength(l) == len &&
        problem_17_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= state && state <= 5 &&
        output_size == Zlength(output_l) &&
        0 <= output_size && output_size <= len + 1 &&
        output_l == music_final_output_z(music_prefix_output_z(len, l), music_prefix_state_z(len, l)) &&
        CharArray::full(music_string, len + 1, app(l, cons(0, nil))) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), output_size) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, len + 1)
    */
    return out;
}
