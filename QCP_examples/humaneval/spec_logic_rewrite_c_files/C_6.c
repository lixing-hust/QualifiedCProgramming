/*
Input to this function is a string represented multiple groups for nested parentheses separated by spaces.
For each of the group, output the deepest level of nesting of parentheses.
E.g. (()()) has maximum two levels of nesting while ((())) has three.

>>> parse_nested_parens("(()()) ((())) () ((())()())")
{2, 3, 1, 3}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "string.h"

/*@ Extern Coq (problem_6_pre_z: list Z -> Prop)
               (problem_6_spec_z: list Z -> list Z -> Prop)
               (valid_paren_depth_input_6: list Z -> Prop)
               (parse_safe_input_6: list Z -> Prop)
               (parse_state_6: list Z -> Z -> Z -> Z -> list Z -> Prop)
               (parse_output_6: list Z -> list Z)
               (Zlength: {A} -> list A -> Z) */
/*@ Import Coq Require Import coins_6 */

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

IntArray *parse_nested_parens(char *paren_string)
/*@ With str_l
    Require
        valid_string(str_l) &&
        all_ascii(str_l) &&
        valid_paren_depth_input_6(str_l) &&
        parse_safe_input_6(str_l) &&
        string_length(str_l) + 1 < INT_MAX &&
        problem_6_pre_z(str_l) &&
        store_string(paren_string, str_l)
    Ensure exists data output_l,
        __return != 0 &&
        data != 0 &&
        output_l == parse_output_6(str_l) &&
        Zlength(output_l) <= string_length(str_l) &&
        problem_6_spec_z(str_l, output_l) &&
        store_string(paren_string, str_l) *
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), Zlength(output_l)) *
        IntArray::seg(data, 0, Zlength(output_l), output_l) *
        IntArray::undef_seg(data, Zlength(output_l), string_length(str_l) + 1)
*/
{
    int n = (int)strlen(paren_string) /*@ where str = str_l */;
    IntArray *out = malloc_int_array_struct();
    int cap = n + 1;
    int *data = malloc_int_array(cap);
    int level = 0;
    int max_level = 0;
    int out_size = 0;
    int ch = 0;

    /*@ Inv Assert exists output_l,
        0 <= i && i <= n &&
        n == string_length(str_l) &&
        cap == n + 1 &&
        paren_string == paren_string@pre &&
        out != 0 &&
        data != 0 &&
        0 <= out_size && out_size <= i &&
        out_size == Zlength(output_l) &&
        0 <= level && level <= i &&
        0 <= max_level && max_level <= i &&
        0 <= ch && ch <= 127 &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        valid_paren_depth_input_6(str_l) &&
        parse_safe_input_6(str_l) &&
        string_length(str_l) + 1 < INT_MAX &&
        problem_6_pre_z(str_l) &&
        parse_state_6(str_l, i, level, max_level, output_l) &&
        store_string(paren_string@pre, str_l) *
        undef_data_at(&(out -> data)) *
        undef_data_at(&(out -> size)) *
        IntArray::seg(data, 0, out_size, output_l) *
        IntArray::undef_seg(data, out_size, cap)
    */
    for (int i = 0; i < n; i++) {
        ch = paren_string[i];
        if (ch == 40) {
            level = level + 1;
            if (level > max_level) {
                max_level = level;
            }
            /*@ Assert exists output_l,
                0 <= i && i < n &&
                n == string_length(str_l) &&
                cap == n + 1 &&
                paren_string == paren_string@pre &&
                out != 0 &&
                data != 0 &&
                ch == 40 &&
                0 <= out_size && out_size <= i &&
                out_size == Zlength(output_l) &&
                1 <= level && level <= i + 1 &&
                1 <= max_level && max_level <= i + 1 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                valid_paren_depth_input_6(str_l) &&
                parse_safe_input_6(str_l) &&
                string_length(str_l) + 1 < INT_MAX &&
                problem_6_pre_z(str_l) &&
                parse_state_6(str_l, i + 1, level, max_level, output_l) &&
                store_string(paren_string@pre, str_l) *
                undef_data_at(&(out -> data)) *
                undef_data_at(&(out -> size)) *
                IntArray::seg(data, 0, out_size, output_l) *
                IntArray::undef_seg(data, out_size, cap)
            */
        } else if (ch == 41) {
            level = level - 1;
            if (level == 0) {
                data[out_size] = max_level;
                out_size = out_size + 1;
                max_level = 0;
                /*@ Assert exists output_l,
                    0 <= i && i < n &&
                    n == string_length(str_l) &&
                    cap == n + 1 &&
                    paren_string == paren_string@pre &&
                    out != 0 &&
                    data != 0 &&
                    ch == 41 &&
                    1 <= out_size && out_size <= i + 1 &&
                    out_size == Zlength(output_l) &&
                    level == 0 &&
                    max_level == 0 &&
                    valid_string(str_l) &&
                    all_ascii(str_l) &&
                    valid_paren_depth_input_6(str_l) &&
                    parse_safe_input_6(str_l) &&
                    string_length(str_l) + 1 < INT_MAX &&
                    problem_6_pre_z(str_l) &&
                    parse_state_6(str_l, i + 1, level, max_level, output_l) &&
                    store_string(paren_string@pre, str_l) *
                    undef_data_at(&(out -> data)) *
                    undef_data_at(&(out -> size)) *
                    IntArray::seg(data, 0, out_size, output_l) *
                    IntArray::undef_seg(data, out_size, cap)
                */
            } else {
                /*@ Assert exists output_l,
                    0 <= i && i < n &&
                    n == string_length(str_l) &&
                    cap == n + 1 &&
                    paren_string == paren_string@pre &&
                    out != 0 &&
                    data != 0 &&
                    ch == 41 &&
                    0 <= out_size && out_size <= i &&
                    out_size == Zlength(output_l) &&
                    0 < level && level <= i &&
                    0 <= max_level && max_level <= i &&
                    valid_string(str_l) &&
                    all_ascii(str_l) &&
                    valid_paren_depth_input_6(str_l) &&
                    parse_safe_input_6(str_l) &&
                    string_length(str_l) + 1 < INT_MAX &&
                    problem_6_pre_z(str_l) &&
                    parse_state_6(str_l, i + 1, level, max_level, output_l) &&
                    store_string(paren_string@pre, str_l) *
                    undef_data_at(&(out -> data)) *
                    undef_data_at(&(out -> size)) *
                    IntArray::seg(data, 0, out_size, output_l) *
                    IntArray::undef_seg(data, out_size, cap)
                */
            }
        } else {
            /*@ Assert exists output_l,
                0 <= i && i < n &&
                n == string_length(str_l) &&
                cap == n + 1 &&
                paren_string == paren_string@pre &&
                out != 0 &&
                data != 0 &&
                ch == 32 &&
                0 <= out_size && out_size <= i &&
                out_size == Zlength(output_l) &&
                0 <= level && level <= i &&
                0 <= max_level && max_level <= i &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                valid_paren_depth_input_6(str_l) &&
                parse_safe_input_6(str_l) &&
                string_length(str_l) + 1 < INT_MAX &&
                problem_6_pre_z(str_l) &&
                parse_state_6(str_l, i + 1, level, max_level, output_l) &&
                store_string(paren_string@pre, str_l) *
                undef_data_at(&(out -> data)) *
                undef_data_at(&(out -> size)) *
                IntArray::seg(data, 0, out_size, output_l) *
                IntArray::undef_seg(data, out_size, cap)
            */
        }
    }

    /*@ Assert exists output_l,
        n == string_length(str_l) &&
        cap == n + 1 &&
        paren_string == paren_string@pre &&
        out != 0 &&
        data != 0 &&
        out_size == Zlength(output_l) &&
        out_size <= n &&
        level == 0 &&
        max_level == 0 &&
        ch == ch &&
        output_l == parse_output_6(str_l) &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        valid_paren_depth_input_6(str_l) &&
        parse_safe_input_6(str_l) &&
        string_length(str_l) + 1 < INT_MAX &&
        problem_6_pre_z(str_l) &&
        problem_6_spec_z(str_l, output_l) &&
        store_string(paren_string@pre, str_l) *
        undef_data_at(&(out -> data)) *
        undef_data_at(&(out -> size)) *
        IntArray::seg(data, 0, out_size, output_l) *
        IntArray::undef_seg(data, out_size, cap)
    */
    out->data = data;
    out->size = out_size;
    /*@ Assert exists output_l,
        n == string_length(str_l) &&
        cap == n + 1 &&
        paren_string == paren_string@pre &&
        out != 0 &&
        data != 0 &&
        out_size == Zlength(output_l) &&
        out_size <= n &&
        level == 0 &&
        max_level == 0 &&
        ch == ch &&
        output_l == parse_output_6(str_l) &&
        problem_6_spec_z(str_l, output_l) &&
        store_string(paren_string@pre, str_l) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), out_size) *
        IntArray::seg(data, 0, out_size, output_l) *
        IntArray::undef_seg(data, out_size, cap)
    */
    return out;
}
