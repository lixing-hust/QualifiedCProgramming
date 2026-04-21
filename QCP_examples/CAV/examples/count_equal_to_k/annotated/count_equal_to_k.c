/*@ Extern Coq (count_equal_to_k_spec : list Z -> Z -> Z) */
/*@ Import Coq Require Import count_equal_to_k */

int count_equal_to_k(int n, int *a, int k)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == count_equal_to_k_spec(l, k) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int ret = 0;

    /*@ Inv
          0 <= i && i <= n &&
          a == a@pre &&
          n == n@pre &&
          k == k@pre &&
          ret == count_equal_to_k_spec(sublist(0, i, l), k) &&
          IntArray::full(a, n, l)
    */
    for (i = 0; i < n; ++i) {
        if (a[i] == k) {
            ret++;
        }
    }

    /*@ Assert
          i == n &&
          a == a@pre &&
          n == n@pre &&
          k == k@pre &&
          ret == count_equal_to_k_spec(l, k) &&
          IntArray::full(a, n, l)
    */
    return ret;
}
