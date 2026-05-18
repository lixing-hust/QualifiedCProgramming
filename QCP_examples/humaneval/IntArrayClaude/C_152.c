/*
Your task is to determine if a person correctly guessed the results of a number of matches.
You are given two arrays of scores and guesses of equal length, where each index shows a match.
Return an array of the same length denoting how far off each guess was. If they have guessed correctly,
the value is 0, and if not, the value is the absolute difference between the guess and the score.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (Zabs: Z -> Z)
               (problem_152_pre_z: list Z -> list Z -> Prop)
               (problem_152_spec_z: list Z -> list Z -> list Z -> Prop)
               (compare_prefix: Z -> list Z -> list Z -> list Z -> Prop)
               (compare_int_range: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_152 */

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

int abs(int x)
/*@ Require
        INT_MIN < x && x <= INT_MAX && emp
    Ensure
        __return == Zabs(x) && emp
*/
{
    if (x < 0) return -x;
    else return x;
}

IntArray *compare(int* game, int game_size, int* guess, int guess_size)
/*@ With game_l guess_l
    Require
        0 <= game_size && game_size < INT_MAX &&
        0 <= guess_size && guess_size < INT_MAX &&
        game_size == Zlength(game_l) &&
        guess_size == Zlength(guess_l) &&
        game_size == guess_size &&
        problem_152_pre_z(game_l, guess_l) &&
        compare_int_range(game_l, guess_l) &&
        IntArray::full(game, game_size, game_l) *
        IntArray::full(guess, guess_size, guess_l)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        data != 0 &&
        output_size == game_size &&
        output_size == Zlength(output_l) &&
        problem_152_spec_z(game_l, guess_l, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(game, game_size, game_l) *
        IntArray::full(guess, guess_size, guess_l) *
        IntArray::full(data, output_size, output_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    int n = game_size < guess_size ? game_size : guess_size;
    out->size = n;
    out->data = malloc_int_array(n);
    int *data = out->data;
    if (data == 0) {
        out->size = 0;
        return out;
    }
    int i;
    /*@ Inv Assert
        exists output_l,
        game == game@pre &&
        guess == guess@pre &&
        game_size == game_size@pre &&
        guess_size == guess_size@pre &&
        out != 0 &&
        data != 0 &&
        n == game_size &&
        n == guess_size &&
        0 <= game_size && game_size < INT_MAX &&
        0 <= guess_size && guess_size < INT_MAX &&
        game_size == Zlength(game_l) &&
        guess_size == Zlength(guess_l) &&
        game_size == guess_size &&
        problem_152_pre_z(game_l, guess_l) &&
        compare_int_range(game_l, guess_l) &&
        0 <= i && i <= n &&
        i == Zlength(output_l) &&
        compare_prefix(i, game_l, guess_l, output_l) &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), n) *
        IntArray::full(game, game_size, game_l) *
        IntArray::full(guess, guess_size, guess_l) *
        IntArray::seg(data, 0, i, output_l) *
        IntArray::undef_seg(data, i, n)
    */
    for (i=0;i<n;i++) {
        int diff;
        int value;
        diff = game[i] - guess[i];
        value = abs(diff);
        data[i] = value;
        /*@ Assert
            exists output_l,
            game == game@pre &&
            guess == guess@pre &&
            game_size == game_size@pre &&
            guess_size == guess_size@pre &&
            out != 0 &&
            data != 0 &&
            n == game_size &&
            n == guess_size &&
            0 <= game_size && game_size < INT_MAX &&
            0 <= guess_size && guess_size < INT_MAX &&
            game_size == Zlength(game_l) &&
            guess_size == Zlength(guess_l) &&
            game_size == guess_size &&
            problem_152_pre_z(game_l, guess_l) &&
            compare_int_range(game_l, guess_l) &&
            0 <= i && i < n &&
            i + 1 == Zlength(output_l) &&
            compare_prefix(i + 1, game_l, guess_l, output_l) &&
            data_at(&(out -> data), data) *
            data_at(&(out -> size), n) *
            data_at(&diff, diff) *
            data_at(&value, value) *
            IntArray::full(game, game_size, game_l) *
            IntArray::full(guess, guess_size, guess_l) *
            IntArray::seg(data, 0, i + 1, output_l) *
            IntArray::undef_seg(data, i + 1, n)
        */
    }
    return out;
}
