#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

void hello(char *out)
/*@ With l
    Require
      CharArray::full(out, 6, l)
    Ensure
      CharArray::full(out, 6,
        cons(104, cons(101, cons(108, cons(108, cons(111, cons(0, nil))))))
      )
*/
{
    out[0] = 'h';
    out[1] = 'e';
    out[2] = 'l';
    out[3] = 'l';
    out[4] = 'o';
    out[5] = '\0';
}
