/*@ Extern Coq (array_equal_spec : list Z -> list Z -> Z) */
/*@ Import Coq Require Import array_equal */

int array_equal(int n, int *a, int *b)
/*@ With la lb
    Require
      0 <= n &&
      Zlength(la) == n &&
      Zlength(lb) == n &&
      IntArray::full(a, n, la) &&
      IntArray::full(b, n, lb)
    Ensure
      __return == array_equal_spec(la, lb) &&
      IntArray::full(a, n, la) &&
      IntArray::full(b, n, lb)
*/
{
    int i;

    /*@ Inv
          0 <= i && i <= n &&
          n == n@pre &&
          a == a@pre &&
          b == b@pre &&
          (forall (j: Z), (0 <= j && j < i) => la[j] == lb[j]) &&
          IntArray::full(a, n, la) &&
          IntArray::full(b, n, lb)
    */
    for (i = 0; i < n; ++i) {
        if (a[i] != b[i]) {
            return 0;
        }
    }

    /*@ Assert
          i == n &&
          n == n@pre &&
          a == a@pre &&
          b == b@pre &&
          (forall (j: Z), (0 <= j && j < n) => la[j] == lb[j]) &&
          IntArray::full(a, n, la) &&
          IntArray::full(b, n, lb)
    */
    return 1;
}
