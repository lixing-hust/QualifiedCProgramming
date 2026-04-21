

#include "poly_sll_def.h"

struct list *reverse(struct list *p) 
/*@ With {A} storeA (l : list A)
    Require sll(storeA, p, l)
    Ensure sll(storeA, __return, rev(l))
*/
{
   struct list *w = (void *)0, *v = p;
   /*@ Assert w == 0 && v == p && p == p@pre &&
              sll(storeA, w, nil) * sll(storeA, v, l)
    */
   /*@ Inv Assert exists l1 l2,
            p == p@pre &&
            l == app(rev(l1), l2) && 
            sll(storeA, w, l1) * sll(storeA, v, l2)
      */
   while (v) {
      /*@ Assert exists l1 l2 x xs vnext vdata,
         p == p@pre &&
         l == app(rev(l1), l2) &&
         v != 0 &&
         l2 == cons(x, xs) &&
         sll(storeA, w, l1) *
         data_at(&(v -> data), vdata) *
         storeA(vdata, x) *
         data_at(&(v -> next), vnext) *
         sll(storeA, vnext, xs)
      */
      struct list *t = v->next;
      v->next = w;
      w = v;
      v = t;
   }
   return w;
}
