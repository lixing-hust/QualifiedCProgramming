int array_last(int n, int *a)
/*@ With l
    Require
      1 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == l[n - 1] &&
      IntArray::full(a, n, l)
*/
{
    return a[n - 1];
}
