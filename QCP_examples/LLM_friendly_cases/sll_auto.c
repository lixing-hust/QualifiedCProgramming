

#include "sll_shape_def.h"

struct list* malloc_list(int data)
/*@ With data0 
    Require data == data0 && emp
    Ensure __return != 0 && __return -> data == data0 && __return -> next == 0
*/;

void free_list(struct list * x)
/*@ With d n 
    Require x -> data == d && x -> next == n
    Ensure emp
*/;

struct list * sll_copy(struct list * x)
/*@ Require listrep(x)
    Ensure  listrep(__return) * listrep(x)
 */
{
    struct list *y, *p, *t;
    if (x == 0) {
      return 0;
    }
    y = malloc_list(x -> data);
    t = y;
    p = x -> next;
    /*@ Inv Assert exists v, x == x@pre && t != 0 && t -> next == 0 && t -> data == v && lseg(x,p) * listrep(p) * lseg(y, t) */
    while (p) {
      t -> next = malloc_list(p -> data);
      t = t -> next;
      p = p -> next;
    }
    return y;
}

void sll_free(struct list * x)
/*@ Require listrep(x)
    Ensure emp
 */
{
    struct list *y;
  /*@ Inv Assert has_permission(&y) * listrep(x) */
    while (x) {
      y = x -> next;
      free_list(x);
      x = y;
    }
}

struct list *reverse(struct list *p) 
/*@ Require listrep(p)
    Ensure listrep(__return)
*/
{
   struct list * w = (void *) 0, * v = p;
  /*@ Inv Assert has_permission(&p) * listrep(w) * listrep(v) */
   while (v) {
      struct list * t = v -> next;
      v -> next = w;
      w = v;
      v = t;
   }
   return w;
}

struct list * append(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct list *t, *u;
    if (x == (struct list*) 0) {
        return y;
    } else {
        t = x;
        u = t->next;
      /*@ Inv Assert exists w, t != 0 && 
            data_at(field_addr(t, next), u) * 
            data_at(field_addr(t, data), w) *
            listrep(y) *
            listrep(u) *
            lseg(x, t)
         */
        while (u) {
            t = u;
            u = t->next;
        }
        t->next = y;
        return x;
    }
}

struct list *merge(struct list *x , struct list *y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct list *z, *t;
    if (x == 0) {
      return y; 
    }
    else {
      z = x;
      t = y;
      /*@ Inv Assert y == t && x != 0 && lseg(z , x) * listrep(x) * listrep(y) */
      while (y) {
        t = y -> next;
        y -> next = x -> next;
        x -> next = y;
        if (y -> next == 0) {
          y -> next = t;
          return z;
        }
        else {
          x = y -> next;
          y = t;
        }
      }
    }
    
    return z;
}


struct list *multi_append(struct list *x, struct list *y, struct list *z)
/*@ Require listrep(x) * listrep(y) * listrep(z)
    Ensure  listrep(__return)
 */
{
    struct list *t, *u;
    if (x == 0) {
        t = append(y , z);
        return t;
    } else {
        t = x;
        u = t->next;
      /*@ Inv Assert exists v, t != 0 &&
            data_at(field_addr(t, data), v) * 
            data_at(field_addr(t, next), u) * 
            listrep(y) *
            listrep(z) * 
            listrep(u) *
            lseg(x, t)
         */
        while (u) {
            if (y) {
              t -> next = y;
              t = y;
              y = y -> next;
              t -> next = u;
              t = u;
              u = u -> next;
            }
            else {
              u = append(u , z);
              t -> next = u;
              return x;   
            }
        }
        t->next = append(y,z);
        return x;
    }
}