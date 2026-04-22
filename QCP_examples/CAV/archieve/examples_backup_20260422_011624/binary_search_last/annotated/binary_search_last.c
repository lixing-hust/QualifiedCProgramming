#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int binary_search_last(int n, int *a, int target)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
      IntArray::full(a, n, l)
    Ensure
      (((__return == -1) &&
        (forall (i: Z), (0 <= i && i < n) => l[i] != target)) ||
       (0 <= __return && __return < n &&
        l[__return] == target &&
        (forall (i: Z), (__return < i && i < n) => l[i] != target))) &&
      IntArray::full(a, n, l)
*/
{
    int left = 0;
    int right = n;
    int mid;

    /*@ Inv
          0 <= left && left <= right && right <= n &&
          a == a@pre &&
          n == n@pre &&
          target == target@pre &&
          n <= INT_MAX &&
          Zlength(l) == n &&
          (forall (i: Z) (j: Z),
            (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
          (forall (j: Z), (0 <= j && j < left) => l[j] <= target) &&
          (forall (j: Z), (right <= j && j < n) => l[j] > target) &&
          ((left == right && left < n) => l[left] > target) &&
          IntArray::full(a, n, l)
    */
    while (left < right) {
        mid = left + (right - left) / 2;
        /*@ Assert
              0 <= left && left <= right && right <= n &&
              left <= mid && mid < right &&
              0 <= mid && mid < n &&
              a == a@pre &&
              n == n@pre &&
              target == target@pre &&
              n <= INT_MAX &&
              Zlength(l) == n &&
              (forall (i: Z) (j: Z),
                (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
              (forall (j: Z), (0 <= j && j < left) => l[j] <= target) &&
              (forall (j: Z), (right <= j && j < n) => l[j] > target) &&
              ((left == right && left < n) => l[left] > target) &&
              IntArray::full(a, n, l)
        */
        if (a[mid] <= target) {
            left = mid + 1;
        } else {
            /*@ Assert
                  l[mid] > target &&
                  0 <= left && left <= right && right <= n &&
                  left <= mid && mid < right &&
                  0 <= mid && mid < n &&
                  a == a@pre &&
                  n == n@pre &&
                  target == target@pre &&
                  n <= INT_MAX &&
                  Zlength(l) == n &&
                  (forall (i: Z) (j: Z),
                    (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
                  (forall (j: Z), (0 <= j && j < left) => l[j] <= target) &&
                  (forall (j: Z), (right <= j && j < n) => l[j] > target) &&
                  ((left == right && left < n) => l[left] > target) &&
                  IntArray::full(a, n, l)
            */
            right = mid;
        }
    }

    if (left > 0 && a[left - 1] == target) {
        return left - 1;
    }
    return -1;
}
