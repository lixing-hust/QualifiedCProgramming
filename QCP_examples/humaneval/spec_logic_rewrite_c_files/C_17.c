/*
Input to this function is a string representing musical notes in a special ASCII format.
Your task is to parse this string and return vector of integers corresponding to how many beats each
note lasts.

Here is a legend:
"o" - whole note, lasts four beats
"o|" - half note, lasts two beats
".|" - quarter note, lasts one beat

>>> parse_music("o o| .| o| o| .| .| .| .| o o")
{4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "string.h"

/*@ Extern Coq (problem_17_pre_z: list Z -> Prop)
               (problem_17_spec_z: list Z -> list Z -> Prop)
               (music_safe_input_17: list Z -> Prop)
               (music_state_17: list Z -> Z -> list Z -> Prop)
               (music_output_17: list Z -> list Z)
               (string_length: list Z -> Z)
               (Zlength: {A} -> list A -> Z) */
/*@ Import Coq Require Import coins_17 */

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
/*@ Require
        size > 0 && size < INT_MAX
    Ensure
        __return != 0 && IntArray::undef_full(__return, size)
*/;

IntArray *parse_music(char *music_string)
/*@ With str_l
    Require
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_17_pre_z(str_l) &&
        music_safe_input_17(str_l) &&
        string_length(str_l) + 1 < INT_MAX &&
        store_string(music_string, str_l)
    Ensure exists data output_l,
        __return != 0 &&
        data != 0 &&
        output_l == music_output_17(str_l) &&
        Zlength(output_l) <= string_length(str_l) + 1 &&
        problem_17_spec_z(str_l, output_l) &&
        store_string(music_string, str_l) *
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), Zlength(output_l)) *
        IntArray::seg(data, 0, Zlength(output_l), output_l) *
        IntArray::undef_seg(data, Zlength(output_l), string_length(str_l) + 1)
*/
{
    int n = (int)strlen(music_string) /*@ where str = str_l */;
    IntArray *out = malloc_int_array_struct();
    int cap = n + 1;
    int *data = malloc_int_array(cap);
    int out_size = 0;
    int ch = 0;
    int next = 0;
    int value = 0;
    int i;

    /*@ Inv Assert exists output_l,
        0 <= i && i <= n &&
        n == string_length(str_l) &&
        cap == n + 1 &&
        music_string == music_string@pre &&
        out != 0 &&
        data != 0 &&
        0 <= out_size && out_size <= i &&
        out_size == Zlength(output_l) &&
        0 <= ch && ch <= 127 &&
        0 <= next && next <= 127 &&
        0 <= value && value <= 4 &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_17_pre_z(str_l) &&
        music_safe_input_17(str_l) &&
        string_length(str_l) + 1 < INT_MAX &&
        music_state_17(str_l, i, output_l) &&
        store_string(music_string@pre, str_l) *
        undef_data_at(&(out -> data)) *
        undef_data_at(&(out -> size)) *
        IntArray::seg(data, 0, out_size, output_l) *
        IntArray::undef_seg(data, out_size, cap)
    */
    for (i = 0; i < n;) {
        ch = music_string[i];
        if (ch == 32) {
            i = i + 1;
            /*@ Assert exists output_l,
                0 <= i && i <= n &&
                n == string_length(str_l) &&
                cap == n + 1 &&
                music_string == music_string@pre &&
                out != 0 &&
                data != 0 &&
                0 <= out_size && out_size <= i &&
                out_size == Zlength(output_l) &&
                ch == 32 &&
                0 <= next && next <= 127 &&
                0 <= value && value <= 4 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_17_pre_z(str_l) &&
                music_safe_input_17(str_l) &&
                string_length(str_l) + 1 < INT_MAX &&
                music_state_17(str_l, i, output_l) &&
                store_string(music_string@pre, str_l) *
                undef_data_at(&(out -> data)) *
                undef_data_at(&(out -> size)) *
                IntArray::seg(data, 0, out_size, output_l) *
                IntArray::undef_seg(data, out_size, cap)
            */
        } else {
            if (ch == 111) {
                if (i + 1 < n) {
                    next = music_string[i + 1];
                } else {
                    next = 0;
                }
                if (next == 124) {
                    value = 2;
                    data[out_size] = value;
                    out_size = out_size + 1;
                    i = i + 2;
                    /*@ Assert exists output_l,
                        0 <= i && i <= n &&
                        n == string_length(str_l) &&
                        cap == n + 1 &&
                        music_string == music_string@pre &&
                        out != 0 &&
                        data != 0 &&
                        1 <= out_size && out_size <= i &&
                        out_size == Zlength(output_l) &&
                        ch == 111 &&
                        next == 124 &&
                        value == 2 &&
                        valid_string(str_l) &&
                        all_ascii(str_l) &&
                        problem_17_pre_z(str_l) &&
                        music_safe_input_17(str_l) &&
                        string_length(str_l) + 1 < INT_MAX &&
                        music_state_17(str_l, i, output_l) &&
                        store_string(music_string@pre, str_l) *
                        undef_data_at(&(out -> data)) *
                        undef_data_at(&(out -> size)) *
                        IntArray::seg(data, 0, out_size, output_l) *
                        IntArray::undef_seg(data, out_size, cap)
                    */
                } else {
                    value = 4;
                    data[out_size] = value;
                    out_size = out_size + 1;
                    i = i + 1;
                    /*@ Assert exists output_l,
                        0 <= i && i <= n &&
                        n == string_length(str_l) &&
                        cap == n + 1 &&
                        music_string == music_string@pre &&
                        out != 0 &&
                        data != 0 &&
                        1 <= out_size && out_size <= i &&
                        out_size == Zlength(output_l) &&
                        ch == 111 &&
                        next != 124 &&
                        0 <= next && next <= 127 &&
                        value == 4 &&
                        valid_string(str_l) &&
                        all_ascii(str_l) &&
                        problem_17_pre_z(str_l) &&
                        music_safe_input_17(str_l) &&
                        string_length(str_l) + 1 < INT_MAX &&
                        music_state_17(str_l, i, output_l) &&
                        store_string(music_string@pre, str_l) *
                        undef_data_at(&(out -> data)) *
                        undef_data_at(&(out -> size)) *
                        IntArray::seg(data, 0, out_size, output_l) *
                        IntArray::undef_seg(data, out_size, cap)
                    */
                }
            } else {
                value = 1;
                data[out_size] = value;
                out_size = out_size + 1;
                i = i + 2;
                /*@ Assert exists output_l,
                    0 <= i && i <= n &&
                    n == string_length(str_l) &&
                    cap == n + 1 &&
                    music_string == music_string@pre &&
                    out != 0 &&
                    data != 0 &&
                    1 <= out_size && out_size <= i &&
                    out_size == Zlength(output_l) &&
                    ch == 46 &&
                    0 <= next && next <= 127 &&
                    value == 1 &&
                    valid_string(str_l) &&
                    all_ascii(str_l) &&
                    problem_17_pre_z(str_l) &&
                    music_safe_input_17(str_l) &&
                    string_length(str_l) + 1 < INT_MAX &&
                    music_state_17(str_l, i, output_l) &&
                    store_string(music_string@pre, str_l) *
                    undef_data_at(&(out -> data)) *
                    undef_data_at(&(out -> size)) *
                    IntArray::seg(data, 0, out_size, output_l) *
                    IntArray::undef_seg(data, out_size, cap)
                */
            }
        }
    }

    out->data = data;
    out->size = out_size;
    /*@ Assert
        n == string_length(str_l) &&
        cap == n + 1 &&
        music_string == music_string@pre &&
        out != 0 &&
        data != 0 &&
        out_size == Zlength(music_output_17(str_l)) &&
        Zlength(music_output_17(str_l)) <= string_length(str_l) + 1 &&
        problem_17_spec_z(str_l, music_output_17(str_l)) &&
        store_string(music_string@pre, str_l) *
        data_at(&i, i) *
        data_at(&ch, ch) *
        data_at(&next, next) *
        data_at(&value, value) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), out_size) *
        IntArray::seg(data, 0, out_size, music_output_17(str_l)) *
        IntArray::undef_seg(data, out_size, cap)
    */
    return out;
}
