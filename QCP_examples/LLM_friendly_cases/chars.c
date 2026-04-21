



void chars_initialize(char *a, int n, char m)
/*@ Require 0 <= n && n < INT_MAX && CharArray::undef_full(a, n)
    Ensure CharArray::full(a, n, repeat_Z(m, n))
*/
{
  int i;
  /*@ Inv Assert
      0 <= i && i <= n@pre &&
      0 <= n@pre && n@pre < INT_MAX &&
      a == a@pre && m == m@pre && n == n@pre &&
      CharArray::full(a@pre, i, repeat_Z(m@pre, i)) *
      CharArray::undef_seg(a@pre, i, n@pre)
  */
  for (i = 0; i < n; i++)
  {
    a[i] = m;
  }
}