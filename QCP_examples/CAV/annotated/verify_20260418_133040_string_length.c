#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

int string_length(char *s)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == n &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 0;

    while (1) {
        if (s[i] == 0) {
            break;
        }
        i++;
    }

    return i;
}
