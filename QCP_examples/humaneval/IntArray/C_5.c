#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void intersperse(const int *numbers, int numbers_size, int delimeter,
         int *out)
/*@ With l outl
    Require 0 <= numbers_size && numbers_size < INT_MAX &&
            IntArray::full(numbers, numbers_size, l) *
        IntArray::undef_full(out, 2 * numbers_size - 1)
    Ensure IntArray::full(numbers, numbers_size, l) * 
       IntArray::full(out, 2 * numbers_size - 1 ,outl)
*/
{
    int k = 0;
    if (numbers_size == 0) {
        return;
    }

    out[k] = numbers[0];
    k = k + 1;

    int i;
    /*@ Inv Assert
            exists out_l,
              1 <= i && i <= numbers_size &&
          k == 2 * i - 1 &&
              IntArray::full(numbers, numbers_size, l) *
          IntArray::seg(out, 0, k, out_l) *
              IntArray::undef_seg(out, k, 2 * numbers_size - 1) &&
          out_l[0] == l[0] &&
          (forall (j: Z), (0 <= j && j < i - 1) =>
             out_l[2 * j + 1] == delimeter &&
             out_l[2 * (j + 1)] == l[j + 1])
    */
    for (i = 1; i < numbers_size; i++) {
        out[k] = delimeter;
        k = k + 1;
        out[k] = numbers[i];
        k = k + 1;
    }

}

