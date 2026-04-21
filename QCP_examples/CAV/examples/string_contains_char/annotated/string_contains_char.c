/*@ Extern Coq (string_contains_char_spec : list Z -> Z -> Z) */
/*@ Import Coq Require Import string_contains_char */

int string_contains_char(char *s, char c)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == string_contains_char_spec(l, c) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 0;

    /*@ Inv exists l1 l2,
          0 <= i && i <= n &&
          s == s@pre &&
          c == c@pre &&
          l == app(l1, l2) &&
          Zlength(l1) == i &&
          string_contains_char_spec(l1, c) == 0 &&
          (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
          CharArray::full(s, n + 1, app(l, cons(0, nil)))
    */
    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] == c) {
            return 1;
        }
        i++;
    }

    return 0;
}
