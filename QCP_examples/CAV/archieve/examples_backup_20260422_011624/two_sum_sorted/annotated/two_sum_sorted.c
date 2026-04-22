#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int two_sum_sorted(int n, int *a, int target)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
      (forall (i: Z) (j: Z),
        (0 <= i && i < j && j < n) =>
          (INT_MIN <= l[i] + l[j] && l[i] + l[j] <= INT_MAX)) &&
      IntArray::full(a, n, l)
    Ensure
      ((__return == 1 &&
        (exists i, exists j,
          0 <= i && i < j && j < n && l[i] + l[j] == target)) ||
       (__return == 0 &&
        (forall (i: Z) (j: Z),
          (0 <= i && i < j && j < n) => l[i] + l[j] != target))) &&
      IntArray::full(a, n, l)
*/
{
    int left = 0;
    int right = n - 1;
    int s;

    /*@ Inv
          0 <= left && left <= n &&
          -1 <= right && right < n &&
          left <= right + 1 &&
          a == a@pre &&
          n == n@pre &&
          target == target@pre &&
          n <= INT_MAX &&
          Zlength(l) == n &&
          (forall (i: Z) (j: Z),
            (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
          (forall (i: Z) (j: Z),
            (0 <= i && i < j && j < n) =>
              (INT_MIN <= l[i] + l[j] && l[i] + l[j] <= INT_MAX)) &&
          (forall (i: Z) (j: Z),
            (0 <= i && i < j && j < n && i < left) =>
              l[i] + l[j] != target) &&
          (forall (i: Z) (j: Z),
            (0 <= i && i < j && j < n && right < j) =>
              l[i] + l[j] != target) &&
          IntArray::full(a, n, l)
    */
    while (left < right) {
        s = a[left] + a[right];
        /*@ Assert
              s == l[left] + l[right] &&
              0 <= left && left < right && right < n &&
              left <= n &&
              -1 <= right &&
              left <= right + 1 &&
              a == a@pre &&
              n == n@pre &&
              target == target@pre &&
              n <= INT_MAX &&
              Zlength(l) == n &&
              (forall (i: Z) (j: Z),
                (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
              (forall (i: Z) (j: Z),
                (0 <= i && i < j && j < n) =>
                  (INT_MIN <= l[i] + l[j] && l[i] + l[j] <= INT_MAX)) &&
              (forall (i: Z) (j: Z),
                (0 <= i && i < j && j < n && i < left) =>
                  l[i] + l[j] != target) &&
              (forall (i: Z) (j: Z),
                (0 <= i && i < j && j < n && right < j) =>
                  l[i] + l[j] != target) &&
              IntArray::full(a, n, l)
        */
        if (s == target) {
            return 1;
        }
        if (s < target) {
            /*@ Assert
                  s == l[left] + l[right] &&
                  l[left] + l[right] < target &&
                  0 <= left && left < right && right < n &&
                  left <= n &&
                  -1 <= right &&
                  left <= right + 1 &&
                  a == a@pre &&
                  n == n@pre &&
                  target == target@pre &&
                  n <= INT_MAX &&
                  Zlength(l) == n &&
                  (forall (i: Z) (j: Z),
                    (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
                  (forall (i: Z) (j: Z),
                    (0 <= i && i < j && j < n) =>
                      (INT_MIN <= l[i] + l[j] && l[i] + l[j] <= INT_MAX)) &&
                  (forall (i: Z) (j: Z),
                    (0 <= i && i < j && j < n && i < left) =>
                      l[i] + l[j] != target) &&
                  (forall (i: Z) (j: Z),
                    (0 <= i && i < j && j < n && right < j) =>
                      l[i] + l[j] != target) &&
                  IntArray::full(a, n, l)
            */
            left++;
        } else {
            /*@ Assert
                  s == l[left] + l[right] &&
                  target < l[left] + l[right] &&
                  0 <= left && left < right && right < n &&
                  left <= n &&
                  -1 <= right &&
                  left <= right + 1 &&
                  a == a@pre &&
                  n == n@pre &&
                  target == target@pre &&
                  n <= INT_MAX &&
                  Zlength(l) == n &&
                  (forall (i: Z) (j: Z),
                    (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
                  (forall (i: Z) (j: Z),
                    (0 <= i && i < j && j < n) =>
                      (INT_MIN <= l[i] + l[j] && l[i] + l[j] <= INT_MAX)) &&
                  (forall (i: Z) (j: Z),
                    (0 <= i && i < j && j < n && i < left) =>
                      l[i] + l[j] != target) &&
                  (forall (i: Z) (j: Z),
                    (0 <= i && i < j && j < n && right < j) =>
                      l[i] + l[j] != target) &&
                  IntArray::full(a, n, l)
            */
            right--;
        }
    }

    return 0;
}
