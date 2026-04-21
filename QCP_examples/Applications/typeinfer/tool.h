
enum TypeOp
{
    AT_ATOM,
    AT_ARROW,
    AT_APP,
    AT_VAR
};

struct atype
{
    enum TypeOp t;
    union
    {
        struct
        {
            struct atype *from;
            struct atype *to;
        } ARROW;
        struct
        {
            struct atype *tfn;
            struct atype *rand;
        } APP;
        struct
        {
            int name;
        } VAR;
        struct
        {
            int name;
        } ATOM;
    } d;
};

/*@ Import Coq Require Import SimpleC.EE.Applications.typeinfer.typeinfer_lib */



/*@ Extern Coq (TypeTree :: *) */
/*@ Extern Coq (sol :: *) */
/*@ Extern Coq
    (store_type : Z -> TypeTree -> Assertion)
    (store_type_aux : Z -> Z -> TypeTree -> Assertion)
    (store_option_type : Z -> option TypeTree -> Assertion)
    (store_solution : Z -> sol -> Assertion)
    (store_compressed_solution : Z -> sol -> Assertion)
    (store_solution_aux : Z -> sol -> Z -> Z -> option TypeTree -> Assertion)
    (unify_rel : TypeTree -> TypeTree -> sol -> sol -> Prop)
    (solution_at : sol -> Z -> TypeTree -> Prop)
    (sol_update : sol -> Z -> TypeTree -> sol)
    (sol_correct_iter : TypeTree -> TypeTree -> sol -> sol -> Prop)
    (TVar : Z -> TypeTree)
    (TAtom : Z -> TypeTree)
    (TArrow : TypeTree -> TypeTree -> TypeTree)
    (TApply : TypeTree -> TypeTree -> TypeTree)
    (repr_rel_node : sol -> TypeTree -> TypeTree -> Prop)
    (not_occur_final: sol -> Z -> TypeTree -> Prop)
    (debug : Assertion)
*/

/*@ include strategies "typeinfer.strategies" */
