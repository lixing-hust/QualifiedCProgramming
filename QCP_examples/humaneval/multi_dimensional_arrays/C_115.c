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
#include "int_ptr_array2_def.h"

/*@ Extern Coq (problem_115_pre_z: list (list Z) -> Z -> Prop)
               (problem_115_spec_z: list (list Z) -> Z -> Z -> Prop)
               (row_sum_prefix_z: list Z -> Z -> Z)
               (trips_prefix_z: list (list Z) -> Z -> Z -> Z)
               (row_trip_z: list Z -> Z -> Z)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import coins_115 */

int max_fill(int** grid, int grid_rows, int grid_cols, int capacity)
/*@ With rows
    Require 1 <= grid_rows && grid_rows <= 100 &&
            1 <= grid_cols && grid_cols <= 100 &&
            1 <= capacity && capacity <= 10 &&
            Zlength(rows) == grid_rows &&
            problem_115_pre_z(rows, capacity) &&
            (forall (i: Z), (0 <= i && i < grid_rows) => (Zlength(rows[i]) == grid_cols)) &&
            (forall (i: Z) (j: Z), (0 <= i && i < grid_rows && 0 <= j && j < grid_cols) => (0 <= rows[i][j] && rows[i][j] <= 1)) &&
            IntPtrArray2::full(grid, grid_rows, rows)
    Ensure problem_115_spec_z(rows, capacity, __return) &&
           IntPtrArray2::full(grid, grid_rows, rows)
*/
{
    int out=0;
    /*@ Inv Assert
        0 <= i && i <= grid_rows@pre &&
        1 <= grid_rows@pre && grid_rows@pre <= 100 &&
        1 <= grid_cols@pre && grid_cols@pre <= 100 &&
        1 <= capacity@pre && capacity@pre <= 10 &&
        grid_rows == grid_rows@pre && grid_cols == grid_cols@pre &&
        grid == grid@pre &&
        capacity == capacity@pre &&
        Zlength(rows) == grid_rows@pre &&
        problem_115_pre_z(rows, capacity@pre) &&
        (forall (r: Z), (0 <= r && r < grid_rows@pre) => (Zlength(rows[r]) == grid_cols@pre)) &&
        (forall (r: Z) (c: Z), (0 <= r && r < grid_rows@pre && 0 <= c && c < grid_cols@pre) => (0 <= rows[r][c] && rows[r][c] <= 1)) &&
        out == trips_prefix_z(rows, i, capacity@pre) &&
        0 <= out && out <= i * grid_cols@pre &&
        IntPtrArray2::full(grid@pre, grid_rows@pre, rows)
    */
    for (int i=0;i<grid_rows;i++)
    {
        int sum=0;
        /*@ Assert
            exists row_ptr,
            0 <= i && i < grid_rows@pre &&
            1 <= grid_rows@pre && grid_rows@pre <= 100 &&
            1 <= grid_cols@pre && grid_cols@pre <= 100 &&
            1 <= capacity@pre && capacity@pre <= 10 &&
            grid_rows == grid_rows@pre && grid_cols == grid_cols@pre &&
            grid == grid@pre &&
            capacity == capacity@pre &&
            sum == sum &&
            Zlength(rows) == grid_rows@pre &&
            problem_115_pre_z(rows, capacity@pre) &&
            (forall (r: Z), (0 <= r && r < grid_rows@pre) => (Zlength(rows[r]) == grid_cols@pre)) &&
            (forall (r: Z) (c: Z), (0 <= r && r < grid_rows@pre && 0 <= c && c < grid_cols@pre) => (0 <= rows[r][c] && rows[r][c] <= 1)) &&
            Zlength(Znth(i, rows, nil)) == grid_cols@pre &&
            sum == 0 &&
            sum == row_sum_prefix_z(Znth(i, rows, nil), 0) &&
            out == trips_prefix_z(rows, i, capacity@pre) &&
            0 <= out && out <= i * grid_cols@pre &&
            IntPtrArray2::missing_i(grid@pre, grid_rows@pre, i, row_ptr, rows) *
            data_at(grid@pre + (i * sizeof(int *)), int *, row_ptr) *
            IntArray::full(row_ptr, Zlength(Znth(i, rows, nil)), Znth(i, rows, nil))
        */
        /*@ Inv Assert
            exists row_ptr,
            0 <= j && j <= grid_cols@pre &&
            1 <= grid_rows@pre && grid_rows@pre <= 100 &&
            1 <= grid_cols@pre && grid_cols@pre <= 100 &&
            1 <= capacity@pre && capacity@pre <= 10 &&
            grid_rows == grid_rows@pre && grid_cols == grid_cols@pre &&
            grid == grid@pre &&
            capacity == capacity@pre &&
            0 <= i && i < grid_rows@pre &&
            Zlength(rows) == grid_rows@pre &&
            problem_115_pre_z(rows, capacity@pre) &&
            (forall (r: Z), (0 <= r && r < grid_rows@pre) => (Zlength(rows[r]) == grid_cols@pre)) &&
            (forall (r: Z) (c: Z), (0 <= r && r < grid_rows@pre && 0 <= c && c < grid_cols@pre) => (0 <= rows[r][c] && rows[r][c] <= 1)) &&
            Zlength(Znth(i, rows, nil)) == grid_cols@pre &&
            sum == row_sum_prefix_z(Znth(i, rows, nil), j) &&
            0 <= sum && sum <= j &&
            out == trips_prefix_z(rows, i, capacity@pre) &&
            0 <= out && out <= i * grid_cols@pre &&
            IntPtrArray2::missing_i(grid@pre, grid_rows@pre, i, row_ptr, rows) *
            data_at(grid@pre + (i * sizeof(int *)), int *, row_ptr) *
            IntArray::full(row_ptr, Zlength(Znth(i, rows, nil)), Znth(i, rows, nil))
        */
        for (int j=0;j<grid_cols;j++)
            sum+=grid[i][j];
        /*@ Assert
            0 <= i && i < grid_rows@pre &&
            1 <= grid_rows@pre && grid_rows@pre <= 100 &&
            1 <= grid_cols@pre && grid_cols@pre <= 100 &&
            1 <= capacity@pre && capacity@pre <= 10 &&
            grid_rows == grid_rows@pre && grid_cols == grid_cols@pre &&
            grid == grid@pre &&
            capacity == capacity@pre &&
            Zlength(rows) == grid_rows@pre &&
            problem_115_pre_z(rows, capacity@pre) &&
            (forall (r: Z), (0 <= r && r < grid_rows@pre) => (Zlength(rows[r]) == grid_cols@pre)) &&
            (forall (r: Z) (c: Z), (0 <= r && r < grid_rows@pre && 0 <= c && c < grid_cols@pre) => (0 <= rows[r][c] && rows[r][c] <= 1)) &&
            Zlength(Znth(i, rows, nil)) == grid_cols@pre &&
            sum == row_sum_prefix_z(Znth(i, rows, nil), grid_cols@pre) &&
            0 <= sum && sum <= grid_cols@pre &&
            out == trips_prefix_z(rows, i, capacity@pre) &&
            0 <= out && out <= i * grid_cols@pre &&
            IntPtrArray2::full(grid@pre, grid_rows@pre, rows)
        */
        if (sum>0)  out+=(sum-1)/capacity+1;
    }
    return out;
}
