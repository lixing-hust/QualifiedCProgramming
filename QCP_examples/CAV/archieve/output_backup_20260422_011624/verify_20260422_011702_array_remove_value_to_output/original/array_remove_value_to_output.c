#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (array_remove_value_to_output_spec : list Z -> Z -> list Z) */
/*@ Import Coq Require Import array_remove_value_to_output */

int array_remove_value_to_output(int n, int *a, int k, int *out)
/*@ With la, lo
    Require
      0 <= n &&
      Zlength(la) == n &&
      Zlength(lo) == n &&
      IntArray::full(a, n, la) *
      IntArray::full(out, n, lo)
    Ensure
      exists t,
        __return == Zlength(array_remove_value_to_output_spec(la, k)) &&
        Zlength(t) == n - Zlength(array_remove_value_to_output_spec(la, k)) &&
        IntArray::full(a, n, la) *
        IntArray::full(out, n, app(array_remove_value_to_output_spec(la, k), t))
*/
{
    int write = 0;
    int i = 0;
    while (i < n) {
        if (a[i] != k) {
            out[write] = a[i];
            write++;
        }
        i++;
    }
    return write;
}
