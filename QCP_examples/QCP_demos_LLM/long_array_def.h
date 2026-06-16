/*@ Extern Coq (sum : list Z -> Z)
               (sublist : {A} -> Z -> Z -> list A -> list A)
               (LongArray::full : Z -> Z -> list Z -> Assertion)
               (LongArray::missing_i: Z -> Z -> Z -> Z -> list Z -> Assertion)
               (LongArray::seg: Z -> Z -> Z -> list Z -> Assertion)
               (LongArray::seg_shape: Z -> Z -> Z -> Assertion)
               (LongArray::full_shape: Z -> Z -> Assertion)
               (LongArray::missing_i_shape : Z -> Z -> Z -> Z -> Assertion)
               (LongArray::undef_full : Z -> Z -> Assertion)
               (LongArray::undef_seg: Z -> Z -> Z -> Assertion)
               (LongArray::undef_missing_i: Z -> Z -> Z -> Z -> Assertion)
               (Znth: {A} -> Z -> list A -> A -> A)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
               (zeros: Z -> list Z)
*/

/*@ include strategies "long_array.strategies" */
