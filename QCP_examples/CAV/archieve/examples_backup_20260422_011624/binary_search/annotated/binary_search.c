#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int binary_search(int n, int *a, int target)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      (forall (i: Z), (0 <= i && i + 1 < n) => l[i] <= l[i + 1]) &&
      IntArray::full(a, n, l)
    Ensure
      (((__return == -1) &&
        (forall (i: Z), (0 <= i && i < n) => l[i] != target)) ||
       ((__return != -1) &&
        0 <= __return && __return < n &&
        l[__return] == target)) &&
      IntArray::full(a, n, l)
*/
{
    int left = 0;
    int right = n - 1;
    int mid;

    /*@ Inv
          0 <= left && left <= n &&
          -1 <= right && right < n &&
          left <= right + 1 &&
          a == a@pre &&
          n == n@pre &&
          target == target@pre &&
          Zlength(l) == n &&
          (forall (i: Z), (0 <= i && i + 1 < n) => l[i] <= l[i + 1]) &&
          (forall (j: Z), (0 <= j && j < left) => l[j] < target) &&
          (forall (j: Z), (right < j && j < n) => target < l[j]) &&
          IntArray::full(a, n, l)
    */
    while (left <= right) {
        mid = left + (right - left) / 2;
        /*@ Assert
              0 <= left && left <= n &&
              -1 <= right && right < n &&
              left <= right + 1 &&
              left <= mid && mid <= right &&
              0 <= mid && mid < n &&
              a == a@pre &&
              n == n@pre &&
              target == target@pre &&
              Zlength(l) == n &&
              (forall (i: Z), (0 <= i && i + 1 < n) => l[i] <= l[i + 1]) &&
              (forall (j: Z), (0 <= j && j < left) => l[j] < target) &&
              (forall (j: Z), (right < j && j < n) => target < l[j]) &&
              IntArray::full(a, n, l)
        */
        if (a[mid] == target) {
            return mid;
        }
        /*@ Assert
              0 <= left && left <= n &&
              -1 <= right && right < n &&
              left <= right + 1 &&
              left <= mid && mid <= right &&
              0 <= mid && mid < n &&
              a == a@pre &&
              n == n@pre &&
              target == target@pre &&
              Zlength(l) == n &&
              l[mid] != target &&
              (forall (i: Z), (0 <= i && i + 1 < n) => l[i] <= l[i + 1]) &&
              (forall (j: Z), (0 <= j && j < left) => l[j] < target) &&
              (forall (j: Z), (right < j && j < n) => target < l[j]) &&
              IntArray::full(a, n, l)
        */
        if (a[mid] < target) {
            left = mid + 1;
        } else {
            /*@ Assert
                  target < l[mid] &&
                  0 <= left && left <= n &&
                  -1 <= right && right < n &&
                  left <= right + 1 &&
                  left <= mid && mid <= right &&
                  0 <= mid && mid < n &&
                  a == a@pre &&
                  n == n@pre &&
                  target == target@pre &&
                  Zlength(l) == n &&
                  (forall (i: Z), (0 <= i && i + 1 < n) => l[i] <= l[i + 1]) &&
                  (forall (j: Z), (0 <= j && j < left) => l[j] < target) &&
                  (forall (j: Z), (right < j && j < n) => target < l[j]) &&
                  IntArray::full(a, n, l)
            */
            right = mid - 1;
        }
    }

    return -1;
}
