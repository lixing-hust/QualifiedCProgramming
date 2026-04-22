#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

/*@ Extern Coq (string_remove_char_to_output_spec : list Z -> Z -> list Z) */
/*@ Import Coq Require Import string_remove_char_to_output */

int string_remove_char_to_output(char *s, char *out, char c)
/*@ With l d n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil))) *
      CharArray::full(out, n + 1, d)
    Ensure
      exists t,
        __return == Zlength(string_remove_char_to_output_spec(l, c)) &&
        Zlength(t) == n - Zlength(string_remove_char_to_output_spec(l, c)) &&
        CharArray::full(s, n + 1, app(l, cons(0, nil))) *
        CharArray::full(out, n + 1, app(app(string_remove_char_to_output_spec(l, c), cons(0, nil)), t))
*/
{
    int i = 0;
    int j = 0;

    /*@ Inv exists l1 l2 d1,
          0 <= i && i <= n &&
          0 <= j && j <= i &&
          s == s@pre &&
          out == out@pre &&
          c == c@pre &&
          l == app(l1, l2) &&
          Zlength(l1) == i &&
          j == Zlength(string_remove_char_to_output_spec(l1, c)) &&
          Zlength(d1) == n + 1 - j &&
          (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
          CharArray::full(s, n + 1, app(l, cons(0, nil))) *
          CharArray::full(out, n + 1, app(string_remove_char_to_output_spec(l1, c), d1))
    */
    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] != c) {
            out[j] = s[i];
            j++;
        }
        i++;
    }

    /*@ Assert exists x t,
          i == n &&
          s == s@pre &&
          out == out@pre &&
          c == c@pre &&
          0 <= j && j <= n &&
          j == Zlength(string_remove_char_to_output_spec(l, c)) &&
          Zlength(t) == n - j &&
          CharArray::full(s, n + 1, app(l, cons(0, nil))) *
          CharArray::full(out, n + 1, app(app(string_remove_char_to_output_spec(l, c), cons(x, nil)), t))
    */
    out[j] = 0;
    return j;
}
