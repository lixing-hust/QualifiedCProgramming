void string_set_a(int n, char *s)
/*@ Require
      0 <= n && n < INT_MAX &&
      CharArray::undef_full(s, n + 1)
    Ensure
      CharArray::full(s, n + 1, app(repeat_Z('a', n), cons(0, nil)))
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        s[i] = 97;
    }
    s[n] = 0;
}
