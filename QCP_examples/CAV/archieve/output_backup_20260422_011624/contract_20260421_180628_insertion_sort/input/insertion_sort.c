#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (Permutation: list Z -> list Z -> Prop)
               (sorted_z: list Z -> Prop) */
/*@ Import Coq Require Import insertion_sort */

void insertion_sort(int n, int *a)
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
    int key;

    for (i = 1; i < n; ++i) {
        key = a[i];
        j = i - 1;
        while (j >= 0 && a[j] > key) {
            a[j + 1] = a[j];
            j--;
        }
        a[j + 1] = key;
    }
}
