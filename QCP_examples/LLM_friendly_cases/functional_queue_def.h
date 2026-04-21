struct queue {
  struct list * l1;
  struct list * l2;
};

/*@ Import Coq Require Import SimpleC.EE.LLM_friendly_cases.functional_queue_lib */

/*@ Extern Coq (store_queue : Z -> list Z -> Assertion)
 */

/*@ include strategies "functional_queue.strategies" */