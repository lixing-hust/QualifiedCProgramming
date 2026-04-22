#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

/*@ Extern Coq (string_replace_char_spec : list Z -> Z -> Z -> list Z) */
/*@ Import Coq Require Import string_replace_char */

void string_replace_char(char *s, char old_c, char new_c)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      CharArray::full(s, n + 1, app(string_replace_char_spec(l, old_c, new_c), cons(0, nil)))
*/
{
    int i = 0;

    /*@ Inv exists l1 l2,
          0 <= i && i <= n &&
          s == s@pre &&
          old_c == old_c@pre &&
          new_c == new_c@pre &&
          l == app(l1, l2) &&
          Zlength(l) == n &&
          Zlength(l1) == i &&
          Zlength(l2) == n - i &&
          (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
          CharArray::full(s, n + 1, app(app(string_replace_char_spec(l1, old_c, new_c), l2), cons(0, nil)))
    */
    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] == old_c) {
            s[i] = new_c;
        }
        i++;
    }
}
