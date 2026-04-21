/*@ Extern Coq (merge_sorted_arrays_spec : list Z -> list Z -> list Z) */
/*@ Import Coq Require Import merge_sorted_arrays */

void merge_sorted_arrays(int n, int *a, int m, int *b, int *out)
/*@ With la lb lo
    Require
      0 <= n &&
      0 <= m &&
      n + m <= INT_MAX &&
      Zlength(la) == n &&
      Zlength(lb) == m &&
      Zlength(lo) == n + m &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => la[i] <= la[j]) &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < m) => lb[i] <= lb[j]) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, m, lb) *
      IntArray::full(out, n + m, lo)
    Ensure
      Zlength(merge_sorted_arrays_spec(la, lb)) == n + m &&
      IntArray::full(a, n, la) *
      IntArray::full(b, m, lb) *
      IntArray::full(out, n + m, merge_sorted_arrays_spec(la, lb))
*/
{
    int i = 0;
    int j = 0;
    int k = 0;

    /*@ Inv exists lout_done,
          0 <= i && i <= n &&
          0 <= j && j <= m &&
          k == i + j &&
          0 <= k && k <= n + m &&
          a == a@pre &&
          b == b@pre &&
          out == out@pre &&
          n == n@pre &&
          m == m@pre &&
          n + m <= INT_MAX &&
          Zlength(la) == n &&
          Zlength(lb) == m &&
          Zlength(lo) == n + m &&
          (forall (ai: Z) (aj: Z),
            (0 <= ai && ai <= aj && aj < n) => Znth(ai, la, 0) <= Znth(aj, la, 0)) &&
          (forall (bi: Z) (bj: Z),
            (0 <= bi && bi <= bj && bj < m) => Znth(bi, lb, 0) <= Znth(bj, lb, 0)) &&
          (forall (bp: Z) (ai: Z),
            (0 <= bp && bp < j && i <= ai && ai < n) => Znth(bp, lb, 0) < Znth(ai, la, 0)) &&
          (forall (ap: Z) (bi: Z),
            (0 <= ap && ap < i && j <= bi && bi < m) => Znth(ap, la, 0) <= Znth(bi, lb, 0)) &&
          Zlength(lout_done) == k &&
          lout_done == merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb)) &&
          IntArray::full(a, n, la) *
          IntArray::full(b, m, lb) *
          IntArray::full(out, n + m, app(lout_done, sublist(k, n + m, lo)))
    */
    while (i < n && j < m) {
        if (a[i] <= b[j]) {
            out[k] = a[i];
            i++;
        } else {
            out[k] = b[j];
            j++;
        }
        k++;
    }

    /*@ Inv Assert exists lout_done,
          0 <= i && i <= n &&
          0 <= j && j <= m &&
          k == i + j &&
          0 <= k && k <= n + m &&
          (i == n || j == m) &&
          a == a@pre &&
          b == b@pre &&
          out == out@pre &&
          n == n@pre &&
          m == m@pre &&
          n + m <= INT_MAX &&
          Zlength(la) == n &&
          Zlength(lb) == m &&
          Zlength(lo) == n + m &&
          (forall (ai: Z) (aj: Z),
            (0 <= ai && ai <= aj && aj < n) => Znth(ai, la, 0) <= Znth(aj, la, 0)) &&
          (forall (bi: Z) (bj: Z),
            (0 <= bi && bi <= bj && bj < m) => Znth(bi, lb, 0) <= Znth(bj, lb, 0)) &&
          (forall (bp: Z) (ai: Z),
            (0 <= bp && bp < j && i <= ai && ai < n) => Znth(bp, lb, 0) < Znth(ai, la, 0)) &&
          (forall (ap: Z) (bi: Z),
            (0 <= ap && ap < i && j <= bi && bi < m) => Znth(ap, la, 0) <= Znth(bi, lb, 0)) &&
          Zlength(lout_done) == k &&
          lout_done == merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb)) &&
          IntArray::full(a, n, la) *
          IntArray::full(b, m, lb) *
          IntArray::full(out, n + m, app(lout_done, sublist(k, n + m, lo)))
    */
    while (i < n) {
        out[k] = a[i];
        i++;
        k++;
    }

    /*@ Inv Assert exists lout_done,
          i == n &&
          0 <= j && j <= m &&
          k == n + j &&
          0 <= k && k <= n + m &&
          a == a@pre &&
          b == b@pre &&
          out == out@pre &&
          n == n@pre &&
          m == m@pre &&
          n + m <= INT_MAX &&
          Zlength(la) == n &&
          Zlength(lb) == m &&
          Zlength(lo) == n + m &&
          (forall (ai: Z) (aj: Z),
            (0 <= ai && ai <= aj && aj < n) => Znth(ai, la, 0) <= Znth(aj, la, 0)) &&
          (forall (bi: Z) (bj: Z),
            (0 <= bi && bi <= bj && bj < m) => Znth(bi, lb, 0) <= Znth(bj, lb, 0)) &&
          (forall (bp: Z) (ai: Z),
            (0 <= bp && bp < j && i <= ai && ai < n) => Znth(bp, lb, 0) < Znth(ai, la, 0)) &&
          (forall (ap: Z) (bi: Z),
            (0 <= ap && ap < i && j <= bi && bi < m) => Znth(ap, la, 0) <= Znth(bi, lb, 0)) &&
          Zlength(lout_done) == k &&
          lout_done == merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb)) &&
          IntArray::full(a, n, la) *
          IntArray::full(b, m, lb) *
          IntArray::full(out, n + m, app(lout_done, sublist(k, n + m, lo)))
    */
    while (j < m) {
        out[k] = b[j];
        j++;
        k++;
    }
}
