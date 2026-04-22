#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void array_reverse_in_place(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      IntArray::full(a, n, rev(l))
*/
{
    int left = 0;
    int right = n - 1;

    /*@ Inv
          0 <= left && -1 <= right &&
          left <= right + 1 &&
          left == n@pre - 1 - right &&
          n == n@pre && a == a@pre &&
          n@pre == Zlength(l) &&
          IntArray::full(a, n@pre,
            app(rev(sublist(right + 1, n@pre, l)),
                app(sublist(left, right + 1, l),
                    rev(sublist(0, left, l)))))
    */
    while (left < right) {
        int tmp = a[left];
        a[left] = a[right];
        a[right] = tmp;
        left++;
        right--;
    }
}
