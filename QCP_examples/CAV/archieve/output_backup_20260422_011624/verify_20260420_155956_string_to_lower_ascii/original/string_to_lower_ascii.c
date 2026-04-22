#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

/*@ Extern Coq (string_to_lower_ascii_spec : list Z -> list Z) */
/*@ Import Coq Require Import string_to_lower_ascii */

void string_to_lower_ascii(char *s)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      CharArray::full(s, n + 1, app(string_to_lower_ascii_spec(l), cons(0, nil)))
*/
{
    int i = 0;

    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (65 <= s[i] && s[i] <= 90) {
            s[i] = s[i] - 65 + 97;
        }
        i++;
    }
}
