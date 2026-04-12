struct queue {
  struct list * head;
  struct list * tail;
};

/*@ Import Coq Require Import SimpleC.EE.LLM_friendly_cases.sll_queue_lib */

/*@ Extern Coq (store_queue : Z -> list Z -> Assertion)
 */

/*@ include strategies "sll_queue.strategies" */
