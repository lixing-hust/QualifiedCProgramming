/*@ Extern Coq (array_contains_spec : list Z -> Z -> Z) */
/*@ Import Coq Require Import array_contains */

int array_contains(int n, int *a, int k)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == array_contains_spec(l, k) &&
      IntArray::full(a, n, l)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] == k) {
            return 1;
        }
    }

    return 0;
}
