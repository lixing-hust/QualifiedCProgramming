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

    for (i = 0; i < n; ++i) {
        min_idx = i;
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
