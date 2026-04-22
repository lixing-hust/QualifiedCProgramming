#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (Permutation: list Z -> list Z -> Prop)
               (sorted_z: list Z -> Prop) */
/*@ Import Coq Require Import selection_sort */

void selection_sort(int n, int *a)
/*@ With l
    Require
      0 <= n && n <= 2000 &&
      IntArray::full(a, n, l)
    Ensure
      exists l0,
        sorted_z(l0) &&
        Permutation(l, l0) &&
        IntArray::full(a, n, l0)
*/
{
    int i;
    int j;
    int min_idx;
    int tmp;

    /*@ Inv
          exists l_outer,
            0 <= i && i <= n@pre &&
            n == n@pre && a == a@pre &&
            Permutation(l, l_outer) &&
            sorted_z(sublist(0, i, l_outer)) &&
            (forall (p: Z),
              (0 <= p && p < i) =>
              (forall (q: Z),
                (i <= q && q < n@pre) =>
                l_outer[p] <= l_outer[q])) &&
            IntArray::full(a, n@pre, l_outer)
    */
    for (i = 0; i < n; ++i) {
        min_idx = i;
        /*@ Inv
              exists l_inner,
                0 <= i && i < n@pre &&
                i + 1 <= j && j <= n@pre &&
                i <= min_idx && min_idx < j &&
                n == n@pre && a == a@pre &&
                Permutation(l, l_inner) &&
                sorted_z(sublist(0, i, l_inner)) &&
                (forall (p: Z),
                  (0 <= p && p < i) =>
                  (forall (q: Z),
                    (i <= q && q < n@pre) =>
                    l_inner[p] <= l_inner[q])) &&
                (forall (k: Z),
                  (i <= k && k < j) =>
                  l_inner[min_idx] <= l_inner[k]) &&
                IntArray::full(a, n@pre, l_inner)
        */
        for (j = i + 1; j < n; ++j) {
            if (a[j] < a[min_idx]) {
                min_idx = j;
            }
        }
        tmp = a[i];
        a[i] = a[min_idx];
        a[min_idx] = tmp;
    }
}
