#include "bst_def.h"


struct tree * malloc_tree_node()
  /*@ Require emp
      Ensure __return != 0 &&
             has_permission(&(__return -> key)) *
             has_permission(&(__return -> value)) *
             has_permission(&(__return -> left)) *
             has_permission(&(__return -> right))
   */;

void insert(struct tree **b, int x, int value)
  /*@ high_level_spec <= low_level_spec
      With m
      Require
        INT_MIN <= x && x <= INT_MAX &&
        Bst::store_map(* b, m)
      Ensure
        Bst::store_map(* b, map_insert(x, value, m))
   */
;

void insert(struct tree **b, int x, int value)
  /*@ low_level_spec
      With tr
      Require
        INT_MIN <= x && x <= INT_MAX &&
        store_tree(* b, tr)
      Ensure
        store_tree(* b, tree_insert(x, value, tr))
   */
{
  /*@ Inv Assert
        exists pt0 tr0,
          x == x@pre && value == value@pre &&
          combine_tree(pt0, tree_insert(x@pre, value@pre, tr0)) ==
            tree_insert(x@pre, value@pre, tr) &&
          store_ptb(b, b@pre, pt0) * store_tree(* b, tr0)
   */
  while (1) {
    struct tree *p;
    p = *b;
    if (p == (void *)0) {
      p = malloc_tree_node();
      p->key = x;
      p->value = value;
      p->left = (void *)0;
      p->right = (void *)0;
      *b = p;
      return;
    } else {
      /*@ Assert
          exists pt0 tr0 l0 r0,
            x == x@pre && value == value@pre &&
            p == * b && p != 0 &&
            combine_tree(pt0, tree_insert(x@pre, value@pre, tr0)) ==
              tree_insert(x@pre, value@pre, tr) &&
            store_ptb(b, b@pre, pt0) *
            store_tree(p, tr0) &&
            INT_MIN <= p -> key && p -> key <= INT_MAX &&
            tr0 == make_tree(l0, p -> key, p -> value, r0) &&
            store_tree(p -> left, l0) *
            store_tree(p -> right, r0)
      */
      int y;
      y = p->key;
      if (x < y) {
        b = &p->left;
      } else if (y < x) {
        b = &p->right;
      } else {
        p->value = value;
        return;
      }
    }
  }
}

