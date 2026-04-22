#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (move_zeroes_to_end_spec: list Z -> list Z) */
/*@ Extern Coq (move_zeroes_nonzeroes: list Z -> list Z) */
/*@ Extern Coq (move_zeroes_zeroes: list Z -> list Z) */
/*@ Import Coq Require Import array_move_zeroes_to_end */

void array_move_zeroes_to_end(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      Zlength(move_zeroes_to_end_spec(l)) == n &&
      IntArray::full(a, n, move_zeroes_to_end_spec(l))
*/
{
    int write = 0;
    int i = 0;
    /*@ Inv exists lc,
          0 <= i && i <= n@pre &&
          0 <= write && write <= i &&
          a == a@pre &&
          n == n@pre &&
          n@pre == Zlength(l) &&
          Zlength(lc) == n@pre &&
          write == Zlength(move_zeroes_nonzeroes(sublist(0, i, l))) &&
          (forall (k: Z),
            (0 <= k && k < write) =>
            lc[k] == move_zeroes_nonzeroes(sublist(0, i, l))[k]) &&
          (forall (k: Z),
            (i <= k && k < n@pre) =>
            lc[k] == l[k]) &&
          IntArray::full(a, n@pre, lc)
    */
    while (i < n) {
        if (a[i] != 0) {
            a[write] = a[i];
            write++;
        }
        i++;
    }
    /*@ Inv exists lc,
          Zlength(move_zeroes_nonzeroes(l)) <= write && write <= n@pre &&
          a == a@pre &&
          n == n@pre &&
          n@pre == Zlength(l) &&
          Zlength(lc) == n@pre &&
          (forall (k: Z),
            (0 <= k && k < Zlength(move_zeroes_nonzeroes(l))) =>
            lc[k] == move_zeroes_nonzeroes(l)[k]) &&
          (forall (k: Z),
            (Zlength(move_zeroes_nonzeroes(l)) <= k && k < write) =>
            lc[k] == 0) &&
          IntArray::full(a, n@pre, lc)
    */
    while (write < n) {
        /*@ exists lc,
              Zlength(move_zeroes_nonzeroes(l)) <= write && write < n@pre &&
              n@pre == Zlength(l) &&
              Zlength(lc) == n@pre &&
              (forall (k: Z),
                (0 <= k && k < Zlength(move_zeroes_nonzeroes(l))) =>
                lc[k] == move_zeroes_nonzeroes(l)[k]) &&
              (forall (k: Z),
                (Zlength(move_zeroes_nonzeroes(l)) <= k && k < write) =>
                lc[k] == 0) &&
              IntArray::full(a, n@pre, lc)
            which implies
              IntArray::missing_i(a, write, 0, n@pre, lc) *
              data_at(a + (write * sizeof(int)), int, lc[write])
        */
        a[write] = 0;
        /*@ exists lc,
              Zlength(move_zeroes_nonzeroes(l)) <= write && write < n@pre &&
              n@pre == Zlength(l) &&
              Zlength(lc) == n@pre &&
              (forall (k: Z),
                (0 <= k && k < Zlength(move_zeroes_nonzeroes(l))) =>
                lc[k] == move_zeroes_nonzeroes(l)[k]) &&
              (forall (k: Z),
                (Zlength(move_zeroes_nonzeroes(l)) <= k && k < write) =>
                lc[k] == 0) &&
              IntArray::missing_i(a, write, 0, n@pre, lc) *
              data_at(a + (write * sizeof(int)), int, 0)
            which implies
              exists lc1,
                Zlength(lc1) == n@pre &&
                (forall (k: Z),
                  (0 <= k && k < Zlength(move_zeroes_nonzeroes(l))) =>
                  lc1[k] == move_zeroes_nonzeroes(l)[k]) &&
                (forall (k: Z),
                  (Zlength(move_zeroes_nonzeroes(l)) <= k && k < write + 1) =>
                  lc1[k] == 0) &&
                IntArray::full(a, n@pre, lc1)
        */
        write++;
    }
}
