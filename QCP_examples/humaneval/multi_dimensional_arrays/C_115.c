/*
You are given a rectangular grid of wells. Each row represents a single well,
&& each 1 in a row represents a single unit of water.
Each well has a corresponding bucket that can be used to extract water from it,
&& all buckets have the same capacity.
Your task is to use the buckets to empty the wells.
Output the number of times you need to lower the buckets.

Example 1:
    Input:
        grid : {{0,0,1,0}, {0,1,0,0}, {1,1,1,1}}
        bucket_capacity : 1
    Output: 6

Example 2:
    Input:
        grid : {{0,0,1,1}, {0,0,0,0}, {1,1,1,1}, {0,1,1,1}}
        bucket_capacity : 2
    Output: 5

Example 3:
    Input:
        grid : {{0,0,0}, {0,0,0}}
        bucket_capacity : 5
    Output: 0

Constraints:
    * all wells have the same length
    * 1 <= grid.length <= 10^2
    * 1 <= grid{:,1}.length <= 10^2
    * grid{i}{j} -> 0 | 1
    * 1 <= capacity <= 10
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "ptr_array_def.h"

/*@ Extern Coq (problem_115_pre_z: list (list Z) -> Z -> Prop)
               (problem_115_spec_z: list (list Z) -> Z -> Z -> Prop)
               (int_matrix_rows_full: list Z -> Z -> list (list Z) -> Assertion)
               (matrix_rect01_z: list (list Z) -> Z -> Prop)
               (matrix_required_trips_prefix_z: Z -> list (list Z) -> Z -> Z)
               (row_sum_prefix_z: Z -> Z -> list Z -> Z) */
/*@ Import Coq Require Import coins_115 */

int max_fill(int **grid, int grid_rows, int grid_cols, int capacity)
/*@ With grid_l row_ptrs
    Require
        1 <= grid_rows && grid_rows <= 100 &&
        1 <= grid_cols && grid_cols <= 100 &&
        1 <= capacity && capacity <= 10 &&
        Zlength(grid_l) == grid_rows &&
        Zlength(row_ptrs) == grid_rows &&
        matrix_rect01_z(grid_l, grid_cols) &&
        problem_115_pre_z(grid_l, capacity) &&
        PtrArray::full(grid, grid_rows, row_ptrs) *
        int_matrix_rows_full(row_ptrs, grid_cols, grid_l)
    Ensure
        problem_115_spec_z(grid_l, capacity, __return) &&
        PtrArray::full(grid, grid_rows, row_ptrs) *
        int_matrix_rows_full(row_ptrs, grid_cols, grid_l)
*/
{
    int out = 0;
    int i;
    int j;
    int sum;
    int *row;

    j = 0;
    sum = 0;
    row = 0;

    /*@ Inv Assert
        0 <= i && i <= grid_rows &&
        1 <= grid_rows && grid_rows <= 100 &&
        1 <= grid_cols && grid_cols <= 100 &&
        1 <= capacity && capacity <= 10 &&
        out == matrix_required_trips_prefix_z(i, grid_l, capacity) &&
        j == j &&
        sum == sum &&
        row == row &&
        Zlength(grid_l) == grid_rows &&
        Zlength(row_ptrs) == grid_rows &&
        matrix_rect01_z(grid_l, grid_cols) &&
        problem_115_pre_z(grid_l, capacity) &&
        PtrArray::full(grid, grid_rows, row_ptrs) *
        int_matrix_rows_full(row_ptrs, grid_cols, grid_l)
    */
    for (i = 0; i < grid_rows; i++) {
        sum = 0;
        row = grid[i];

        /*@ Inv Assert
            0 <= i && i < grid_rows &&
            0 <= j && j <= grid_cols &&
            row == row_ptrs[i] &&
            sum == row_sum_prefix_z(j, grid_cols, grid_l[i]) &&
            1 <= grid_rows && grid_rows <= 100 &&
            1 <= grid_cols && grid_cols <= 100 &&
            1 <= capacity && capacity <= 10 &&
            out == matrix_required_trips_prefix_z(i, grid_l, capacity) &&
            Zlength(grid_l) == grid_rows &&
            Zlength(row_ptrs) == grid_rows &&
            matrix_rect01_z(grid_l, grid_cols) &&
            problem_115_pre_z(grid_l, capacity) &&
            PtrArray::full(grid, grid_rows, row_ptrs) *
            int_matrix_rows_full(row_ptrs, grid_cols, grid_l)
        */
        for (j = 0; j < grid_cols; j++)
            sum += row[j];
        if (sum > 0) out += (sum - 1) / capacity + 1;
    }
    return out;
}
