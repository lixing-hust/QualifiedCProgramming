#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

void string_copy(char *src, char *dst)
/*@ With l d n
    Require
      0 <= n && n < INT_MAX &&
      CharArray::full(src, n + 1, app(l, cons(0, nil))) *
      CharArray::full(dst, n + 1, d)
    Ensure
      CharArray::full(src, n + 1, app(l, cons(0, nil))) *
      CharArray::full(dst, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 0;

    while (src[i] != '\0') {
        dst[i] = src[i];
        i++;
    }
    dst[i] = '\0';
}
