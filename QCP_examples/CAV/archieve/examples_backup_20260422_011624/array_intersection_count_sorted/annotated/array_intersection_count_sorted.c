#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (array_intersection_count_sorted_spec : list Z -> list Z -> Z) */
/*@ Import Coq Require Import array_intersection_count_sorted */

int array_intersection_count_sorted(int n, int *a, int m, int *b)
/*@ With la lb
    Require
      0 <= n &&
      n <= INT_MAX &&
      0 <= m &&
      m <= INT_MAX &&
      Zlength(la) == n &&
      Zlength(lb) == m &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => la[i] <= la[j]) &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < m) => lb[i] <= lb[j]) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, m, lb)
    Ensure
      __return == array_intersection_count_sorted_spec(la, lb) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, m, lb)
*/
{
    int i = 0;
    int j = 0;
    int count = 0;
    /*@ Inv
          0 <= i && i <= n &&
          0 <= j && j <= m &&
          0 <= count && count <= i &&
          count <= j &&
          a == a@pre &&
          b == b@pre &&
          n == n@pre &&
          m == m@pre &&
          n <= INT_MAX &&
          m <= INT_MAX &&
          Zlength(la) == n &&
          Zlength(lb) == m &&
          (forall (ai: Z) (aj: Z),
            (0 <= ai && ai <= aj && aj < n) => Znth(ai, la, 0) <= Znth(aj, la, 0)) &&
          (forall (bi: Z) (bj: Z),
            (0 <= bi && bi <= bj && bj < m) => Znth(bi, lb, 0) <= Znth(bj, lb, 0)) &&
          count + array_intersection_count_sorted_spec(sublist(i, n, la), sublist(j, m, lb)) ==
            array_intersection_count_sorted_spec(la, lb) &&
          IntArray::full(a, n, la) *
          IntArray::full(b, m, lb)
    */
    while (i < n && j < m) {
        if (a[i] == b[j]) {
            count++;
            i++;
            j++;
        } else if (a[i] < b[j]) {
            i++;
        } else {
            j++;
        }
    }
    return count;
}
