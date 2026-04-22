#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

int string_ends_with_char(char *s, char c)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      ((n == 0 && __return == 0) ||
       (0 < n && l[n - 1] == c && __return == 1) ||
       (0 < n && l[n - 1] != c && __return == 0)) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 0;

    if (s[0] == 0) {
        return 0;
    }

    /*@ Assert
          0 < n &&
          n < INT_MAX &&
          i == 0 &&
          s == s@pre &&
          c == c@pre &&
          (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
          CharArray::full(s, n + 1, app(l, cons(0, nil)))
    */
    /*@ Inv
          0 <= i && i < n &&
          n < INT_MAX &&
          s == s@pre &&
          c == c@pre &&
          (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
          CharArray::full(s, n + 1, app(l, cons(0, nil)))
    */
    while (1) {
        if (s[i + 1] == 0) {
            break;
        }
        i++;
    }

    /*@ Assert
          0 < n &&
          0 <= i && i < n &&
          n < INT_MAX &&
          i == n - 1 &&
          s == s@pre &&
          c == c@pre &&
          (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
          CharArray::full(s, n + 1, app(l, cons(0, nil)))
    */
    if (s[i] == c) {
        return 1;
    }
    return 0;
}
