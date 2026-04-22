#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

/*@ Extern Coq (string_count_not_char_spec : list Z -> Z -> Z) */
/*@ Import Coq Require Import string_count_not_char */

int string_count_not_char(char *s, char c)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == string_count_not_char_spec(l, c) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 0;
    int count = 0;

    /*@ Inv exists l1 l2,
          0 <= i && i <= n &&
          s == s@pre &&
          c == c@pre &&
          l == app(l1, l2) &&
          Zlength(l1) == i &&
          count == string_count_not_char_spec(l1, c) &&
          (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
          CharArray::full(s, n + 1, app(l, cons(0, nil)))
    */
    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] != c) {
            count++;
        }
        i++;
    }

    /*@ Assert
          i == n &&
          s == s@pre &&
          c == c@pre &&
          count == string_count_not_char_spec(l, c) &&
          CharArray::full(s, n + 1, app(l, cons(0, nil)))
    */
    return count;
}
