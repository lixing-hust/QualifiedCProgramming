

#include "sll_def.h"

/*@ Extern Coq (count: list Z -> Z -> Z)
 */

int length(struct list *p)
/*@ With (l: list Z)
    Require sll(p, l) && Zlength(l) <= 2147483647
    Ensure __return == Zlength(l) && sll(p@pre, l)
*/
{
   int n = 0;
  /*@ Inv Assert
          exists l1 l2,
            l == app(l1, l2) && 
            Zlength(l) <= 2147483647 && 
            n == Zlength(l1) &&
            sllseg(p@pre, p, l1) * sll(p, l2)
      */
   while (p) {
          /*@ Assert exists l1 l2 l3 pnext pdata,
            l == app(l1, l2) &&
            n == Zlength(l1) &&
            p != 0 &&
            l2 == cons(pdata, l3) &&
            Zlength(l) <= 2147483647 &&
            store(&(p -> data), pdata) *
            store(&(p -> next), pnext) *
            sllseg(p@pre, p, l1) * sll(pnext, l3)
      */
      n++;
      p = p -> next;
   }
   return n;
}

struct list *reverse(struct list *p) 
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure sll(__return, rev(l))
*/
{
   struct list * w = (void *) 0, * v = p;
  /*@ Inv Assert
          exists l1 l2,
            p == p@pre &&
            l == app(rev(l1), l2) && 
            sll(w, l1) * sll(v, l2)
      */
   while (v) {
          /*@ Assert exists l1 l2 l2_new vnext vdata,
        p == p@pre &&
        l == app(rev(l1), l2) &&
        v != 0 &&
            l2 == cons(vdata, l2_new) &&
            sll(w, l1) *
            store(&(v -> data), vdata) *
            store(&(v -> next), vnext) *
            sll(vnext, l2_new)
      */
      struct list * t = v -> next;
      v -> next = w;
      w = v;
      v = t;
   }
   return w;
}

struct list *reverse_alter_style1(struct list *p) 
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure sll(__return, rev(l))
*/
{
   struct list * w = (void *) 0, * v = p;
   /*@ Inv Assert
      exists l1 l2,
      p == p@pre &&
            l == app(rev(l1), l2) && 
            sll(w, l1) * sll(v, l2)
      */
   while (v) {
    /*@ Assert exists l1 l2 x xs vn,
    p == p@pre &&
      l == app(rev(l1), l2) &&
      v != 0 &&
      l2 == cons(x, xs) &&
      sll(w, l1) *
      store(&(v -> data), x) *
      store(&(v -> next), vn) *
      sll(vn, xs)
    */
      struct list * t = v->next;
      v->next = w;
      w = v;
      v = t;
   }
   return w;
}

struct list *reverse_alter_style2(struct list *p) 
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure sll(__return, rev(l))
*/
{
   struct list * w = (void *) 0, * v = p;
  /*@ Inv Assert
      exists l1 l2 w_inv v_inv,
      p == p@pre &&
      l == app(rev(l1), l2) &&
      store(&w, w_inv) *
      store(&v, v_inv) *
      sll(w_inv, l1) *
      sll(v_inv, l2)
  */
   while (v) {
    /*@ Assert exists l1 l2 w_inv v_inv x xs v_inv_next,
    p == p@pre &&
      l == app(rev(l1), l2) &&
      v_inv != 0 &&
      l2 == cons(x, xs) &&
      store(&w, w_inv) *
      store(&v, v_inv) *
      sll(w_inv, l1) *
      store(&(v_inv -> data), x) *
      store(&(v_inv -> next), v_inv_next) *
      sll(v_inv_next, xs)
    */
      struct list * t = v -> next;
      v->next = w;
      w = v;
      v = t;
   }
   return w;
}

struct list *reverse_alter_style3(struct list *p) 
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure sll(__return, rev(l))
*/
{
   struct list *w;
   struct list *v;
   w = (void *)0;
   v = p;
   /*@ Assert w == 0 && v == p && p == p@pre && sll(w, nil) * sll(v, l) */
  /*@ Inv Assert exists l1 l2,
            p == p@pre && l == app(rev(l1), l2) && 
            sll(w, l1) * sll(v, l2)
      */
   while (v) {
          /*@ Assert exists l1 l2 l2_new vnext vdata,
        p == p@pre &&
        l == app(rev(l1), l2) &&
        v != 0 &&
            l2 == cons(vdata, l2_new) &&
            sll(w, l1) *
            store(&(v -> data), vdata) *
            store(&(v -> next), vnext) *
            sll(vnext, l2_new)
      */
      struct list *t;
      t = v->next;
      v->next = w;
      w = v;
      v = t;
   }
   return w;
}

struct list *append(struct list *x, struct list *y)
/*@ With l1 l2
    Require sll(x, l1) * sll(y, l2)
    Ensure sll(__return, app(l1, l2))
*/
{
  struct list *t, *u;
  if (x == (void *)0) {
    return y;
  } else {
        /*@ Assert exists a l1n xn,
          x != 0 && x == x@pre && y == y@pre &&
          l1 == cons(a, l1n) &&
          has_ptr_permission(&t) * has_ptr_permission(&u) *
          store(&(x -> data), a) *
          store(&(x -> next), xn) *
          sll(xn, l1n) * sll(y, l2)
    */
    t = x;
    u = t -> next;
    /*@ Inv Assert
          exists l1a l1b,
            app(l1a, cons(t -> data, l1b)) == l1 &&
            x == x@pre && y == y@pre && x != 0 &&
            t != 0 && t -> next == u &&
            sllseg(x, t, l1a) *
            sll(u, l1b) * sll(y, l2)
    */
    while (u != (void *)0) {
      /*@ Assert exists l1a l1b l1b_new udata unext,
        app(l1a, cons(t -> data, l1b)) == l1 &&
        t != 0 && t -> next == u &&
        u != 0 && x == x@pre && y == y@pre && x != 0 &&
        l1b == cons(udata, l1b_new) &&
        sllseg(x, t, l1a) *
        store(&(u -> data), udata) *
        store(&(u -> next), unext) *
        sll(unext, l1b_new) * sll(y, l2)
      */
      t = u;
      u = t -> next;
    }
    t -> next = y;
    return x;
  }
}

struct list *append_long(struct list *x, struct list *y)
/*@ With l1 l2
    Require sll(x, l1) * sll(y, l2)
    Ensure sll(__return, app(l1, l2))
*/
{
  struct list *t, *u;
  if (x == (void *)0) {
    return y;
  } else {
        /*@ Assert exists a l1b xn,
          x != 0 && x == x@pre && y == y@pre &&
          l1 == cons(a, l1b) &&
              has_ptr_permission(&t) * has_ptr_permission(&u) *
          store(&(x -> data), a) *
          store(&(x -> next), xn) *
          sll(xn, l1b) * sll(y, l2)
    */
    u = x -> next;
    if (u == (void *)0) {
      x -> next = y;
      return x;
    }
    t = x;
    u = t -> next;
    /*@ Inv Assert
          exists l1a b l1c,
            app(l1a, cons(b, l1c)) == l1 &&
            t -> data == b &&
            t -> next == u && 
            t != 0 && x == x@pre && y == y@pre &&
            x != 0 &&
            sllseg(x, t, l1a) *
            sll(u, l1c) * sll(y, l2)
    */
    while (u != (void *)0) {
      /*@ Assert exists l1a b l1c l1d c un,
        app(l1a, cons(b, l1c)) == l1 &&
        t -> data == b &&
        t -> next == u &&
        t != 0 && x == x@pre && y == y@pre && x != 0 &&
        u != 0 &&
        l1c == cons(c, l1d) &&
        store(&(u -> data), c) *
        store(&(u -> next), un) *
        sllseg(x, t, l1a) * sll(un, l1d) * sll(y, l2)
      */
      t = u;
      u = t -> next;
    }
    t -> next = y;
    return x;
  }
}

struct list *append_2p(struct list *x, struct list *y)
/*@ With l1 l2
    Require sll(x, l1) * sll(y, l2)
    Ensure sll(__return, app(l1, l2))
*/
{
  struct list * * pres = & x, * * pt = pres;
  /*@ Inv Assert
        exists l1a l1b ptv ptvv,
            app(l1a, l1b) == l1 &&
            pres == &x && y == y@pre &&
            store(&pt, ptv) * 
            store(ptv, struct list *, ptvv) *
            sllbseg(pres, ptv, l1a) *
            sll(ptvv, l1b) * sll(y, l2)
    */
  while (* pt) {
    pt = &((* pt) -> next);
  }
  * pt = y;
  /*@ Assert 
     exists presv ptv,
     y == y@pre &&
     store(&pres, &x) *
     store(&x, presv) *
     store(&pt, ptv) *
     sllseg(presv, y, l1) * 
     sll(y, l2)
  */
  return * pres;
}