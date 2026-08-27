/*
Given a string representing a space separated lowercase letters, return a map
of the letter with the most repetition && containing the corresponding count.
If several letters have the same occurrence, return all of them.

Example:
histogram("a b c") == {{"a", 1}, {"b", 1}, {"c", 1}}
histogram("a b b a") == {{"a", 2}, {"b", 2}}
histogram("a b c a b") == {{"a", 2}, {"b", 2}}
histogram("b b b b a") == {{"b", 4}}
histogram("") == {}

*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_111_pre_z: list Z -> Prop)
               (problem_111_spec_z: list Z -> list Z -> list Z -> Prop)
               (histogram_scan_state_111: list Z -> Z -> list Z -> Z -> Prop)
               (histogram_counts_bounded_111: list Z -> Z -> Prop)
               (histogram_output_state_111: list Z -> Z -> Z -> list Z -> list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (valid_string: list Z -> Prop)
               (Zlength: {A} -> list A -> Z)
               (Znth: {A} -> Z -> list A -> A -> A) */
/*@ Import Coq Require Import coins_111 */

typedef struct {
    char* keys;
    int* values;
    int size;
} CharIntMap;

CharIntMap *malloc_char_int_map_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> keys)) *
           undef_data_at(&(__return -> values)) *
           undef_data_at(&(__return -> size))
*/;

char *malloc_char_array(int size)
/*@ Require 0 <= size && size < INT_MAX && emp
    Ensure __return != 0 && CharArray::undef_full(__return, size)
*/;

int *malloc_int_array(int size)
/*@ Require 0 <= size && size < INT_MAX && emp
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

CharIntMap *histogram(const char* test)
/*@ With input_l n
    Require
        0 <= n && n < INT_MAX &&
        Zlength(input_l) == n &&
        valid_string(input_l) &&
        ascii_range_z(input_l) &&
        problem_111_pre_z(input_l) &&
        CharArray::full(test, n + 1, app(input_l, cons(0, nil)))
    Ensure exists keys values keys_l values_l output_size,
        __return != 0 &&
        keys != 0 && values != 0 &&
        0 <= output_size && output_size <= 256 &&
        output_size == Zlength(keys_l) &&
        output_size == Zlength(values_l) &&
        problem_111_spec_z(input_l, keys_l, values_l) &&
        data_at(&(__return -> keys), keys) *
        data_at(&(__return -> values), values) *
        data_at(&(__return -> size), output_size) *
        CharArray::full(test, n + 1, app(input_l, cons(0, nil))) *
        CharArray::seg(keys, 0, output_size, keys_l) *
        CharArray::undef_seg(keys, output_size, 256) *
        IntArray::seg(values, 0, output_size, values_l) *
        IntArray::undef_seg(values, output_size, 256)
*/
{
    int count[256];
    int init;
    /*@ Inv Assert
        0 <= init && init <= 256 &&
        0 <= n && n < INT_MAX &&
        test == test@pre &&
        Zlength(input_l) == n &&
        valid_string(input_l) &&
        ascii_range_z(input_l) &&
        problem_111_pre_z(input_l) &&
        CharArray::full(test@pre, n + 1, app(input_l, cons(0, nil))) *
        IntArray::seg(count, 0, init, zeros(init)) *
        IntArray::undef_seg(count, init, 256)
    */
    for (init = 0; init < 256; init = init + 1) {
        count[init] = 0;
    }

    CharIntMap *out = malloc_char_int_map_struct();
    int max = 0;
    out->keys = malloc_char_array(256);
    out->values = malloc_int_array(256);
    out->size = 0;
    char *keys = out->keys;
    int *values = out->values;

    int i;
    int ch = 0;
    int next_count = 0;
    /*@ Inv Assert
        exists count_l,
        test == test@pre &&
        out != 0 && keys != 0 && values != 0 &&
        init == init &&
        ch == ch &&
        next_count == next_count &&
        n < INT_MAX &&
        Zlength(input_l) == n &&
        0 <= i && i <= n &&
        0 <= max && max <= i &&
        Zlength(count_l) == 256 &&
        histogram_scan_state_111(input_l, i, count_l, max) &&
        histogram_counts_bounded_111(count_l, i) &&
        valid_string(input_l) &&
        ascii_range_z(input_l) &&
        problem_111_pre_z(input_l) &&
        data_at(&(out -> keys), keys) *
        data_at(&(out -> values), values) *
        data_at(&(out -> size), 0) *
        CharArray::full(test@pre, n + 1, app(input_l, cons(0, nil))) *
        IntArray::full(count, 256, count_l) *
        CharArray::undef_full(keys, 256) *
        IntArray::undef_full(values, 256)
    */
    for (i = 0; test[i] != '\0'; i = i + 1) {
        if (test[i] != ' ') {
            ch = (unsigned char)test[i];
            /*@ Assert
                exists count_l,
                test == test@pre &&
                out != 0 && keys != 0 && values != 0 &&
                init == init &&
                0 <= i && i < n &&
                0 <= ch && ch < 256 &&
                ch != 32 &&
                ch == Znth(i, input_l, 0) &&
                n < INT_MAX &&
                Zlength(input_l) == n &&
                0 <= max && max <= i &&
                next_count == next_count &&
                Zlength(count_l) == 256 &&
                histogram_scan_state_111(input_l, i, count_l, max) &&
                histogram_counts_bounded_111(count_l, i) &&
                valid_string(input_l) &&
                ascii_range_z(input_l) &&
                problem_111_pre_z(input_l) &&
                data_at(&(out -> keys), keys) *
                data_at(&(out -> values), values) *
                data_at(&(out -> size), 0) *
                CharArray::full(test@pre, n + 1, app(input_l, cons(0, nil))) *
                IntArray::full(count, 256, count_l) *
                CharArray::undef_full(keys, 256) *
                IntArray::undef_full(values, 256)
            */
            next_count = count[ch] + 1;
            count[ch] = next_count;
            if (next_count > max) max = next_count;
        }
    }

    int scan;
    int selected_count = 0;
    int output_size = 0;
    /*@ Inv Assert
        exists count_l keys_l values_l,
        test == test@pre &&
        out != 0 && keys != 0 && values != 0 &&
        init == init && i == i && ch == ch && next_count == next_count &&
        selected_count == selected_count &&
        output_size == output_size &&
        n < INT_MAX &&
        Zlength(input_l) == n &&
        0 <= scan && scan <= 256 &&
        0 <= output_size && output_size <= scan &&
        output_size == Zlength(keys_l) &&
        output_size == Zlength(values_l) &&
        Zlength(count_l) == 256 &&
        histogram_scan_state_111(input_l, n, count_l, max) &&
        histogram_counts_bounded_111(count_l, n) &&
        histogram_output_state_111(count_l, max, scan, keys_l, values_l) &&
        valid_string(input_l) &&
        ascii_range_z(input_l) &&
        problem_111_pre_z(input_l) &&
        data_at(&(out -> keys), keys) *
        data_at(&(out -> values), values) *
        data_at(&(out -> size), output_size) *
        CharArray::full(test@pre, n + 1, app(input_l, cons(0, nil))) *
        IntArray::full(count, 256, count_l) *
        CharArray::seg(keys, 0, output_size, keys_l) *
        CharArray::undef_seg(keys, output_size, 256) *
        IntArray::seg(values, 0, output_size, values_l) *
        IntArray::undef_seg(values, output_size, 256)
    */
    for (scan = 0; scan < 256; scan = scan + 1) {
        /*@ Assert
            exists count_l keys_l values_l,
            test == test@pre &&
            out != 0 && keys != 0 && values != 0 &&
            init == init && i == i && ch == ch && next_count == next_count &&
            selected_count == selected_count &&
            n < INT_MAX &&
            Zlength(input_l) == n &&
            0 <= scan && scan < 256 &&
            0 <= output_size && output_size <= scan &&
            output_size == Zlength(keys_l) &&
            output_size == Zlength(values_l) &&
            Zlength(count_l) == 256 &&
            histogram_scan_state_111(input_l, n, count_l, max) &&
            histogram_counts_bounded_111(count_l, n) &&
            histogram_output_state_111(count_l, max, scan, keys_l, values_l) &&
            valid_string(input_l) &&
            ascii_range_z(input_l) &&
            problem_111_pre_z(input_l) &&
            data_at(&(out -> keys), keys) *
            data_at(&(out -> values), values) *
            data_at(&(out -> size), output_size) *
            CharArray::full(test@pre, n + 1, app(input_l, cons(0, nil))) *
            IntArray::full(count, 256, count_l) *
            CharArray::seg(keys, 0, output_size, keys_l) *
            CharArray::undef_seg(keys, output_size, 256) *
            IntArray::seg(values, 0, output_size, values_l) *
            IntArray::undef_seg(values, output_size, 256)
        */
        selected_count = count[scan];
        if (selected_count == max && max > 0) {
            keys[output_size] = (char)scan;
            values[output_size] = selected_count;
            output_size = output_size + 1;
            out->size = output_size;
        }
    }
    return out;
}
