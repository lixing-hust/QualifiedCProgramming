struct queue {
  struct list * head;
  struct list * tail;
};

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.sll_queue_lib */

/*@ Extern Coq (store_queue : Z -> list Z -> Assertion)
 */

/*@ include strategies "sll_queue.strategies" */
