/*
 * Return every coordinate of x in a ragged int matrix.  Rows are visited in
 * ascending order and columns in each row in descending order.
 *
 * The original growing realloc buffer is deliberately replaced by two scans:
 * the first counts the matching cells, and the second fills one exact buffer.
 */
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "int_ptr_array2_def.h"

/*@ Extern Coq (problem_87_pre_z: list (list Z) -> Z -> Prop)
               (problem_87_spec_z: list (list Z) -> Z -> list (Z * Z) -> Prop)
               (get_row_safe_87: list (list Z) -> Prop)
               (row_sizes_87: list (list Z) -> list Z)
               (count_scan_outer_87: list (list Z) -> Z -> Z -> Z -> Prop)
               (count_scan_inner_87: list (list Z) -> Z -> Z -> Z -> Z -> Prop)
               (fill_scan_outer_87: list (list Z) -> Z -> Z -> list (Z * Z) -> Prop)
               (fill_scan_inner_87: list (list Z) -> Z -> Z -> Z -> list (Z * Z) -> Prop)
               (coords_flat_87: list (Z * Z) -> list Z)
               (get_row_finished_87: list (list Z) -> Z -> list (Z * Z) -> Prop)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z) */
/*@ Import Coq Require Import coins_87 */

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
/*@ Require 0 <= size && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

IntArray *get_row(int **lst, const int *row_sizes, int rows, int x)
/*@ With input_l
    Require
        0 <= rows && rows < INT_MAX &&
        rows == Zlength(input_l) &&
        problem_87_pre_z(input_l, x) &&
        get_row_safe_87(input_l) &&
        IntPtrArray2::full(lst, rows, input_l) &&
        IntArray::full(row_sizes, rows,
          row_sizes_87(input_l))
    Ensure
        exists data coords data_l size,
        __return != 0 && data != 0 &&
        0 <= size && 2 * size == Zlength(data_l) &&
        size == Zlength(coords) &&
        coords_flat_87(coords) == data_l &&
        problem_87_spec_z(input_l, x, coords) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), size) *
        IntArray::full(data, 2 * size, data_l) *
        IntPtrArray2::full(lst, rows, input_l) *
        IntArray::full(row_sizes, rows,
          row_sizes_87(input_l))
*/
{
    int count = 0;

    /*@ Inv Assert
        0 <= i && i <= rows@pre &&
        rows == rows@pre && x == x@pre &&
        lst == lst@pre && row_sizes == row_sizes@pre &&
        rows@pre == Zlength(input_l) &&
        problem_87_pre_z(input_l, x@pre) &&
        get_row_safe_87(input_l) &&
        count_scan_outer_87(input_l, x@pre, i, count) &&
        0 <= count && 2 * count < INT_MAX &&
        IntPtrArray2::full(lst@pre, rows@pre, input_l) *
        IntArray::full(row_sizes@pre, rows@pre,
          row_sizes_87(input_l))
    */
    for (int i = 0; i < rows; i++) {
        int row_len = row_sizes[i];
        /*@ Assert
            exists row_ptr,
            0 <= i && i < rows@pre &&
            rows == rows@pre && x == x@pre &&
            lst == lst@pre && row_sizes == row_sizes@pre &&
            rows@pre == Zlength(input_l) &&
            problem_87_pre_z(input_l, x@pre) &&
            get_row_safe_87(input_l) &&
            count_scan_outer_87(input_l, x@pre, i, count) &&
            row_len == Zlength(Znth(i, input_l, nil)) &&
            0 <= row_len && row_len < INT_MAX &&
            0 <= count && 2 * count < INT_MAX &&
            IntPtrArray2::missing_i(lst@pre, rows@pre, i, row_ptr, input_l) *
            data_at(lst@pre + (i * sizeof(int *)), int *, row_ptr) *
            IntArray::full(row_ptr, row_len, Znth(i, input_l, nil)) *
            IntArray::full(row_sizes@pre, rows@pre,
              row_sizes_87(input_l))
        */
        /*@ Inv Assert
            exists row_ptr,
            0 <= i && i < rows@pre &&
            -1 <= j && j < row_len &&
            rows == rows@pre && x == x@pre &&
            lst == lst@pre && row_sizes == row_sizes@pre &&
            rows@pre == Zlength(input_l) &&
            problem_87_pre_z(input_l, x@pre) &&
            get_row_safe_87(input_l) &&
            count_scan_inner_87(input_l, x@pre, i, j, count) &&
            row_len == Zlength(Znth(i, input_l, nil)) &&
            0 <= row_len && row_len < INT_MAX &&
            0 <= count && 2 * count < INT_MAX &&
            IntPtrArray2::missing_i(lst@pre, rows@pre, i, row_ptr, input_l) *
            data_at(lst@pre + (i * sizeof(int *)), int *, row_ptr) *
            IntArray::full(row_ptr, row_len, Znth(i, input_l, nil)) *
            IntArray::full(row_sizes@pre, rows@pre,
              row_sizes_87(input_l))
        */
        for (int j = row_len - 1; j >= 0; j--) {
            if (lst[i][j] == x) count++;
        }
    }

    IntArray *out = malloc_int_array_struct();
    int *data = malloc_int_array(2 * count);
    int size = 0;

    /*@ Inv Assert
        exists coords,
        0 <= i && i <= rows@pre &&
        rows == rows@pre && x == x@pre &&
        lst == lst@pre && row_sizes == row_sizes@pre &&
        rows@pre == Zlength(input_l) &&
        problem_87_pre_z(input_l, x@pre) &&
        get_row_safe_87(input_l) &&
        count_scan_outer_87(input_l, x@pre, rows@pre, count) &&
        fill_scan_outer_87(input_l, x@pre, i, coords) &&
        0 <= count && 2 * count < INT_MAX &&
        0 <= size && size == Zlength(coords) && size <= count &&
        out != 0 && data != 0 &&
        IntArray::seg(data, 0, 2 * size, coords_flat_87(coords)) *
        IntArray::undef_seg(data, 2 * size, 2 * count) *
        undef_data_at(&(out -> data)) * undef_data_at(&(out -> size)) *
        IntPtrArray2::full(lst@pre, rows@pre, input_l) *
        IntArray::full(row_sizes@pre, rows@pre,
          row_sizes_87(input_l))
    */
    for (int i = 0; i < rows; i++) {
        int row_len = row_sizes[i];
        /*@ Assert
            exists row_ptr coords,
            0 <= i && i < rows@pre &&
            rows == rows@pre && x == x@pre &&
            lst == lst@pre && row_sizes == row_sizes@pre &&
            rows@pre == Zlength(input_l) &&
            problem_87_pre_z(input_l, x@pre) &&
            get_row_safe_87(input_l) &&
            count_scan_outer_87(input_l, x@pre, rows@pre, count) &&
            fill_scan_outer_87(input_l, x@pre, i, coords) &&
            row_len == Zlength(Znth(i, input_l, nil)) &&
            0 <= row_len && row_len < INT_MAX &&
            0 <= count && 2 * count < INT_MAX &&
            0 <= size && size == Zlength(coords) && size <= count &&
            out != 0 && data != 0 &&
            IntArray::seg(data, 0, 2 * size, coords_flat_87(coords)) *
            IntArray::undef_seg(data, 2 * size, 2 * count) *
            undef_data_at(&(out -> data)) * undef_data_at(&(out -> size)) *
            IntPtrArray2::missing_i(lst@pre, rows@pre, i, row_ptr, input_l) *
            data_at(lst@pre + (i * sizeof(int *)), int *, row_ptr) *
            IntArray::full(row_ptr, row_len, Znth(i, input_l, nil)) *
            IntArray::full(row_sizes@pre, rows@pre,
              row_sizes_87(input_l))
        */
        /*@ Inv Assert
            exists row_ptr coords,
            0 <= i && i < rows@pre &&
            -1 <= j && j < row_len &&
            rows == rows@pre && x == x@pre &&
            lst == lst@pre && row_sizes == row_sizes@pre &&
            rows@pre == Zlength(input_l) &&
            problem_87_pre_z(input_l, x@pre) &&
            get_row_safe_87(input_l) &&
            count_scan_outer_87(input_l, x@pre, rows@pre, count) &&
            fill_scan_inner_87(input_l, x@pre, i, j, coords) &&
            row_len == Zlength(Znth(i, input_l, nil)) &&
            0 <= row_len && row_len < INT_MAX &&
            0 <= count && 2 * count < INT_MAX &&
            0 <= size && size == Zlength(coords) && size <= count &&
            out != 0 && data != 0 &&
            IntArray::seg(data, 0, 2 * size, coords_flat_87(coords)) *
            IntArray::undef_seg(data, 2 * size, 2 * count) *
            undef_data_at(&(out -> data)) * undef_data_at(&(out -> size)) *
            IntPtrArray2::missing_i(lst@pre, rows@pre, i, row_ptr, input_l) *
            data_at(lst@pre + (i * sizeof(int *)), int *, row_ptr) *
            IntArray::full(row_ptr, row_len, Znth(i, input_l, nil)) *
            IntArray::full(row_sizes@pre, rows@pre,
              row_sizes_87(input_l))
        */
        for (int j = row_len - 1; j >= 0; j--) {
            if (lst[i][j] == x) {
                /*@ Assert
                    exists row_ptr coords,
                    0 <= i && i < rows@pre &&
                    0 <= j && j < row_len &&
                    rows == rows@pre && x == x@pre &&
                    lst == lst@pre && row_sizes == row_sizes@pre &&
                    rows@pre == Zlength(input_l) &&
                    problem_87_pre_z(input_l, x@pre) &&
                    get_row_safe_87(input_l) &&
                    count_scan_outer_87(input_l, x@pre, rows@pre, count) &&
                    fill_scan_inner_87(input_l, x@pre, i, j, coords) &&
                    Znth(j, Znth(i, input_l, nil), 0) == x@pre &&
                    row_len == Zlength(Znth(i, input_l, nil)) &&
                    0 <= row_len && row_len < INT_MAX &&
                    0 <= count && 2 * count < INT_MAX &&
                    0 <= size && size == Zlength(coords) && size < count &&
                    out != 0 && data != 0 &&
                    IntArray::seg(data, 0, 2 * size, coords_flat_87(coords)) *
                    IntArray::undef_seg(data, 2 * size, 2 * count) *
                    undef_data_at(&(out -> data)) * undef_data_at(&(out -> size)) *
                    IntPtrArray2::missing_i(lst@pre, rows@pre, i, row_ptr, input_l) *
                    data_at(lst@pre + (i * sizeof(int *)), int *, row_ptr) *
                    IntArray::full(row_ptr, row_len, Znth(i, input_l, nil)) *
                    IntArray::full(row_sizes@pre, rows@pre,
                      row_sizes_87(input_l))
                */
                data[2 * size] = i;
                data[2 * size + 1] = j;
                size++;
            }
        }
    }

    /*@ Assert
        exists coords,
        rows == rows@pre && x == x@pre &&
        lst == lst@pre && row_sizes == row_sizes@pre &&
        rows@pre == Zlength(input_l) &&
        problem_87_pre_z(input_l, x@pre) &&
        get_row_safe_87(input_l) &&
        count_scan_outer_87(input_l, x@pre, rows@pre, count) &&
        fill_scan_outer_87(input_l, x@pre, rows@pre, coords) &&
        get_row_finished_87(input_l, x@pre, coords) &&
        0 <= count && 2 * count < INT_MAX &&
        0 <= size && size == Zlength(coords) && size == count &&
        out != 0 && data != 0 &&
        IntArray::full(data, 2 * size, coords_flat_87(coords)) *
        undef_data_at(&(out -> data)) * undef_data_at(&(out -> size)) *
        IntPtrArray2::full(lst@pre, rows@pre, input_l) *
        IntArray::full(row_sizes@pre, rows@pre,
          row_sizes_87(input_l))
    */
    out->data = data;
    out->size = size;
    return out;
}
