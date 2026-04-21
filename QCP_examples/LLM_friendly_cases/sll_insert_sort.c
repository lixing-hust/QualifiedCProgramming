

#include "sll_def.h"

/*@ Import Coq Require Import SimpleC.EE.LLM_friendly_cases.sll_insert_sort_lib */

/*@ Extern Coq (Permutation: list Z -> list Z -> Prop)
               (increasing: list Z -> Prop)
               (insert: Z -> list Z -> list Z)
               (strict_upperbound: Z -> list Z -> Prop)
 */

struct list * insertion(struct list * p, struct list * node)
  /*@ With l a
      Require node != 0 && node->data == a && 
              sll(p, l) * 
              undef_data_at(&(node->next), struct list*) 
      Ensure exists l0,
              l0 == insert(a, l) && sll(__return, l0)
   */
{
  struct list * res = p;
  struct list * * p2 = & res;
  /*@ Inv Assert
    exists l1 l2,
      node == node@pre && p == p@pre &&
      node != (void *)0 &&
      l == app(l1, l2) &&
      node->data == a &&
      strict_upperbound(a, l1) &&
      sllbseg(&res, p2, l1) * sll(*p2, l2) *
      undef_data_at(&(node->next), struct list*)
  */
  while (* p2 != (void * )0 && (* p2) -> data < node -> data) {
    p2 = &((* p2) -> next);
  }
  /*@ Assert
      (exists l1,
        node == node@pre && p == p@pre &&
        node != (void *)0 &&
        l == app(l1, nil) &&
        node->data == a &&
        strict_upperbound(a, l1) &&
        sllbseg(&res, p2, l1) *
        data_at(p2, struct list*, (void *)0) *
        undef_data_at(&(node->next), struct list*))
      ||
      (exists l1 x l0 u unext,
        node == node@pre && p == p@pre &&
        node != (void *)0 &&
        u != (void *)0 &&
        x >= a &&
        l == app(l1, cons(x, l0)) &&
        node->data == a &&
        strict_upperbound(a, l1) &&
        sllbseg(&res, p2, l1) *
        data_at(p2, struct list*, u) *
        data_at(&(u->data), x) *
        data_at(&(u->next), struct list*, unext) *
        sll(unext, l0) *
        undef_data_at(&(node->next), struct list*))
  */
  node -> next = * p2;
  * p2 = node;
  /*@ Assert
      (exists resv l1,
        node == node@pre && p == p@pre &&
        node != (void *)0 &&
        l == app(l1, nil) &&
        strict_upperbound(a, l1) &&
        data_at(&p2, struct list**, p2) *
        data_at(&res, struct list*, resv) *
        sllseg(resv, node, l1) *
        data_at(&(node->data), a) *
        data_at(&(node->next), struct list*, (void *)0))
      ||
      (exists resv l1 x l0 u unext,
        node == node@pre && p == p@pre &&
        node != (void *)0 &&
        u != (void *)0 &&
        x >= a &&
        l == app(l1, cons(x, l0)) &&
        strict_upperbound(a, l1) &&
        data_at(&p2, struct list**, p2) *
        data_at(&res, struct list*, resv) *
        sllseg(resv, node, l1) *
          data_at(&(node->data), a) *
        data_at(&(node->next), struct list*, u) *
        data_at(&(u->data), x) *
        data_at(&(u->next), struct list*, unext) *
        sll(unext, l0))
  */
  return res;
}

struct list * insertion_sort(struct list * x)
  /*@ With l
      Require sll(x, l)
      Ensure exists l0,
               Permutation(l, l0) && increasing(l0) &&
               sll(__return, l0)
   */
{
  struct list * res = (void *)0, * p = x, * q;
  /*@ Inv Assert
    exists l0 l1 l2,
      l == app(l1, l2) && x == x@pre && 
      Permutation(l1, l0) && increasing(l0) &&
      has_ptr_permission(&q) *
      sll(res, l0) * sll(p, l2)
  */
  while (p != (void * )0) {
    q = p -> next;
    res = insertion(res, p);
    p = q;
  }
  return res;
}
