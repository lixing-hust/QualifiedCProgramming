/*@ Extern Coq (Permutation: list Z -> list Z -> Prop)
               (sorted_z: list Z -> Prop) */
/*@ Import Coq Require Import bubble_sort */

void bubble_sort(int *a, int n)
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
    int i, j;

    /*@ Inv
          exists l_outer,
            0 <= i && i <= n@pre &&
            n == n@pre && a == a@pre &&
            Permutation(l, l_outer) &&
            sorted_z(sublist(n@pre - i, n@pre, l_outer)) &&
            (forall (p: Z),
              (0 <= p && p < n@pre - i) =>
              (forall (q: Z),
                (n@pre - i <= q && q < n@pre) =>
                l_outer[p] <= l_outer[q])) &&
            IntArray::full(a, n@pre, l_outer)
    */
    for (i = 0; i < n; ++i) {
        /*@ Inv
              exists l_inner,
                0 <= i && i < n@pre &&
                0 <= j && j <= n@pre - i - 1 &&
                n == n@pre && a == a@pre &&
                Permutation(l, l_inner) &&
                sorted_z(sublist(n@pre - i, n@pre, l_inner)) &&
                (forall (p: Z),
                  (0 <= p && p < n@pre - i) =>
                  (forall (q: Z),
                    (n@pre - i <= q && q < n@pre) =>
                    l_inner[p] <= l_inner[q])) &&
                (forall (k: Z),
                  (0 <= k && k <= j) =>
                  l_inner[k] <= l_inner[j]) &&
                IntArray::full(a, n@pre, l_inner)
        */
        for (j = 0; j + 1 < n - i; ++j) {
            if (a[j] > a[j + 1]) {
                int t = a[j];
                a[j] = a[j + 1];
                a[j + 1] = t;
            }
        }
    }
}
