#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

/*@ Extern Coq (string_equal_spec : list Z -> list Z -> Z) */
/*@ Import Coq Require Import string_equal */

int string_equal(char *a, char *b)
/*@ With la lb na nb
    Require
      0 <= na && na < INT_MAX &&
      0 <= nb && nb < INT_MAX &&
      (forall (k: Z), (0 <= k && k < na) => la[k] != 0) &&
      (forall (k: Z), (0 <= k && k < nb) => lb[k] != 0) &&
      CharArray::full(a, na + 1, app(la, cons(0, nil))) *
      CharArray::full(b, nb + 1, app(lb, cons(0, nil)))
    Ensure
      __return == string_equal_spec(la, lb) &&
      CharArray::full(a, na + 1, app(la, cons(0, nil))) *
      CharArray::full(b, nb + 1, app(lb, cons(0, nil)))
*/
{
    int i = 0;

    /*@ Inv
          0 <= i &&
          i <= na &&
          i <= nb &&
          a == a@pre &&
          b == b@pre &&
          (forall (k: Z), (0 <= k && k < na) => Znth(k, la, 0) != 0) &&
          (forall (k: Z), (0 <= k && k < nb) => Znth(k, lb, 0) != 0) &&
          (forall (j: Z), (0 <= j && j < i) => Znth(j, la, 0) == Znth(j, lb, 0)) &&
          CharArray::full(a, na + 1, app(la, cons(0, nil))) *
          CharArray::full(b, nb + 1, app(lb, cons(0, nil)))
    */
    while (1) {
        if (a[i] == 0 || b[i] == 0) {
            break;
        }
        if (a[i] != b[i]) {
            return 0;
        }
        i++;
    }

    /*@ Assert
          0 <= i &&
          i <= na &&
          i <= nb &&
          a == a@pre &&
          b == b@pre &&
          (i == na || i == nb) &&
          (forall (k: Z), (0 <= k && k < na) => Znth(k, la, 0) != 0) &&
          (forall (k: Z), (0 <= k && k < nb) => Znth(k, lb, 0) != 0) &&
          (forall (j: Z), (0 <= j && j < i) => Znth(j, la, 0) == Znth(j, lb, 0)) &&
          CharArray::full(a, na + 1, app(la, cons(0, nil))) *
          CharArray::full(b, nb + 1, app(lb, cons(0, nil)))
    */
    if (a[i] == 0 && b[i] == 0) {
        /*@ Assert
              i == na &&
              i == nb &&
              a == a@pre &&
              b == b@pre &&
              (forall (k: Z), (0 <= k && k < na) => Znth(k, la, 0) != 0) &&
              (forall (k: Z), (0 <= k && k < nb) => Znth(k, lb, 0) != 0) &&
              (forall (j: Z), (0 <= j && j < i) => Znth(j, la, 0) == Znth(j, lb, 0)) &&
              CharArray::full(a, na + 1, app(la, cons(0, nil))) *
              CharArray::full(b, nb + 1, app(lb, cons(0, nil)))
        */
        return 1;
    }
    return 0;
}
