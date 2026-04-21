void string_set_a(int n, char *s)
/*@ Require
      0 <= n && n < INT_MAX &&
      CharArray::undef_full(s, n + 1)
    Ensure
      CharArray::full(s, n + 1, app(repeat_Z(97, n), cons(0, nil)))
*/
{
    int i;

    /*@ Inv
          0 <= i && i <= n &&
          n == n@pre &&
          s == s@pre &&
          CharArray::full(s, i, repeat_Z(97, i)) *
          CharArray::undef_seg(s, i, n + 1)
    */
    for (i = 0; i < n; ++i) {
        s[i] = 97;
    }
    s[n] = 0;
}
