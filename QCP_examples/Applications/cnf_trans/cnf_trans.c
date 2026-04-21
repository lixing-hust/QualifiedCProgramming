


#include "cnf_trans.h"

/*@ Import Coq  Require Import smt_lang_lib */
/*@ Import Coq  Require Import cnf_trans_lib */
/*@ Import Coq  Require Import malloc */
/*@ Import Coq  Require Import super_poly_sll2 */

/*@ Extern Coq (smt_prop :: *) */
/*@ Extern Coq (PreData :: *) */
/*@ Extern Coq (prop2cnf_ret :: *) */
/*@ Extern Coq (SmtPropBop :: *) */
/*@ Extern Coq (SmtPropUop :: *) */
/*@ Extern Coq (store_SmtProp : Z ->  smt_prop -> Assertion)
               (store_SmtProp' : Z ->  smt_prop -> Assertion)
               (store_SmtProp_cell : Z ->  smt_prop -> Assertion)
               (sll_SmtProplist : Z -> list  smt_prop -> Assertion)
               (sllseg_SmtProplist : Z -> list  smt_prop -> Assertion)
               (sllbseg_SmtProplist : Z -> list  smt_prop -> Assertion)
               (store_cnf_list_cell : Z -> list Z -> Assertion)
               (sll_cnf_list : Z -> list (list Z) -> Assertion)
               (sllseg_cnf_list : Z -> list (list Z) -> Assertion)
               (sllbseg_cnf_list : Z -> list (list Z) -> Assertion)
               (store_predata : Z -> list (list Z) -> Z -> Z -> Assertion)
               (iff2cnf_binary : Z -> Z -> Z -> SmtPropBop -> list (list Z))
               (iff2cnf_unary : Z -> Z -> list (list Z))
               (iff2cnf_length_binary : Z -> Z -> Z -> SmtPropBop -> Z)
               (SmtPBID : SmtPropBop -> Z)
               (SmtPUID : SmtPropUop -> Z)
               (SmtPTID :  smt_prop -> Z)
               (all_zero_list : Z -> list Z)
               (prop_cnt_inf : list (list Z) -> Z)
               (prop_cnt_inf_SmtProp :  smt_prop -> Z)
               (prop2cnf_logic:  smt_prop -> PreData -> prop2cnf_ret)
               (make_predata : list (list Z) -> Z -> Z -> PreData)
               (make_prop2cnf_ret: PreData -> Z ->prop2cnf_ret)
               (SmtB : SmtPropBop -> smt_prop -> smt_prop -> smt_prop)
               (SmtU : SmtPropUop -> smt_prop -> smt_prop)
               (SmtV : Z -> smt_prop)
               (SmtProp_size : smt_prop -> Z)
               */

/* BEGIN Given Functions */

// 分配一个大小为size的全零的int数组
int *malloc_int_array(int size)
    /*@ Require size > 0
        Ensure __return != 0 &&
               IntArray::full(__return, size, all_zero_list(size))
     */
    ;

// 释放int数组
void free_int_array(int *array)
    /*@ Require exists n l, array != 0 && n > 0 &&
                  IntArray::full(array, n, l)
      Ensure emp
    */
    ;

// 分配一个初始全零 cnf_list 结构体
cnf_list *malloc_cnf_list()
    /*@ Require emp
        Ensure __return != 0 &&
               data_at(&(__return -> size), 0) *
               data_at(&(__return -> clause), 0) *
               data_at(&(__return -> next), 0)
      */
    ;

// 释放 cnf_list 结构体
void free_cnf_list(cnf_list *list)
    /*@ Require list != 0 && exists s c n,
               data_at(&(list -> size), s) *
               data_at(&(list -> clause), c) *
               data_at(&(list -> next), n)
        Ensure emp
      */
    ;

/* END Given Functions */

void clause_gen_unary(int p2, int p3, PreData *data)
/*@ With clist pcnt ccnt max_size
      Require p2 != 0 && p3 != 0 && prop_cnt_inf(clist) + 1 <= pcnt && p2 <=
              pcnt && p3 <= pcnt && -p2 <= pcnt && -p3 <= pcnt &&
              Zlength(clist) <= max_size && max_size <= 40000 &&
              pcnt <= 40000 &&
              store_predata(data, clist, pcnt, ccnt)
      Ensure Zlength(clist) <= max_size && max_size <= 40000 &&
             store_predata(data, app(iff2cnf_unary(p2, p3), clist), pcnt,
             ccnt + 2)
*/
{
  int size = 3;
  int *clause1 = malloc_int_array(size);
  int *clause2 = malloc_int_array(size);
  // 完成 SET_PROP: p3<->(p1 op p2) / p3<->not p2

  // p3\/p2
  clause1[0] = p2;
  clause1[1] = p3;
  // 非p3\/非p2
  clause2[0] = -p2;
  clause2[1] = -p3;

  cnf_list *list1 = malloc_cnf_list();
  cnf_list *list2 = malloc_cnf_list();
  list1->size = size;
  list2->size = size;
  list1->clause = clause1;
  list2->clause = clause2;

  list1->next = list2;

  /*@ store_predata(data@pre, clist, pcnt, ccnt)
      which implies
      data@pre != 0 && Zlength(clist) == ccnt &&
      exists y,
        data_at(&(data@pre -> cnf_res), y) *
        data_at(&(data@pre -> prop_cnt), pcnt) *
        data_at(&(data@pre -> clause_cnt), ccnt) *
        sll_cnf_list(y, clist)
   */

  list2->next = data->cnf_res;
  data->cnf_res = list1;
  data->clause_cnt += 2;
}

// 生成p3<->(p1 op p2)对应的cnf中的clause
// p3<->not p2 (op为 not时， 此时p1缺省为0)
void clause_gen_binary(int p1, int p2, int p3, int op, PreData *data)
/*@ With clist pcnt ccnt bop max_size
      Require p1 != 0 && p2 != 0 && p3 != 0 && p1 <= pcnt && p2 <=
              pcnt && p3 <= pcnt && -p1 <= pcnt && -p2 <= pcnt &&
              -p3 <= pcnt &&
              prop_cnt_inf(clist) + 1 <= pcnt && op == SmtPBID(bop) &&
              Zlength(clist) <= max_size && max_size <= 40000 &&
              pcnt <= 40000 &&
              store_predata(data, clist, pcnt, ccnt)
      Ensure Zlength(clist) <= max_size && max_size <= 40000 &&
             store_predata(data, app(iff2cnf_binary(p1, p2, p3, bop),
                           clist), pcnt, ccnt + iff2cnf_length_binary(p1, p2,
                                                                      p3, bop))
*/
{
  int size = 3;
  int *clause1 = malloc_int_array(size);
  int *clause2 = malloc_int_array(size);
  int *clause3 = malloc_int_array(size);
  int *clause4 = malloc_int_array(size);
  // 完成 SET_PROP: p3<->(p1 op p2) / p3<->not p2
  int cnt = 0;
  switch (op) {
    case SMTPROP_OR: {
      // p3\/非p1
      clause1[0] = -p1;
      clause1[1] = p3;
      // p3\/非p2
      clause2[0] = -p2;
      clause2[1] = p3;
      if (p1 != p2) {
        // 非p3\/p1\/p2
        clause3[0] = p1;
        clause3[1] = p2;
        clause3[2] = -p3;
      } else {
        clause3[0] = p1;
        clause3[1] = -p3;
      }
      cnt += 3;
      break;
    }
    case SMTPROP_AND: {
      // 非p3\/p1
      clause1[0] = p1;
      clause1[1] = -p3;
      // 非p3\/p2
      clause2[0] = p2;
      clause2[1] = -p3;
      if (p1 != p2) {
        // p3\/非p1\/非p2
        clause3[0] = -p1;
        clause3[1] = -p2;
        clause3[2] = p3;
      } else {
        clause3[0] = -p1;
        clause3[1] = p3;
      }
      cnt += 3;
      break;
    }
    case SMTPROP_IMPLY: {
      if (p1 != p2) {
        // p3\/p1
        clause1[0] = p1;
        clause1[1] = p3;
        // p3\/非p2
        clause2[0] = -p2;
        clause2[1] = p3;
        // 非p3\/非p1\/p2
        clause3[0] = -p1;
        clause3[1] = p2;
        clause3[2] = -p3;
        cnt += 3;
      } else {
        clause1[0] = p3;
        cnt += 1;
      }
      break;
    }
    case SMTPROP_IFF: {
      if (p1 != p2) {
        // p3\/p1\/p2
        clause1[0] = p1;
        clause1[1] = p2;
        clause1[2] = p3;
        // p3\/非p1\/非p2
        clause2[0] = -p1;
        clause2[1] = -p2;
        clause2[2] = p3;
        // 非p3\/p1\/非p2
        clause3[0] = p1;
        clause3[1] = -p2;
        clause3[2] = -p3;
        // 非p3\/非p1\/p2
        clause4[0] = -p1;
        clause4[1] = p2;
        clause4[2] = -p3;
        cnt += 4;
      } else {
        clause1[0] = p3;
        cnt += 1;
      }
      break;
    }
    default: {
      // unreachable
      /*@ Branch clear all
       */
    }
  }
  cnf_list *list1 = malloc_cnf_list();
  cnf_list *list2 = malloc_cnf_list();
  cnf_list *list3 = malloc_cnf_list();
  cnf_list *list4 = malloc_cnf_list();
  list1->size = size;
  list2->size = size;
  list3->size = size;
  list4->size = size;
  list1->clause = clause1;
  list2->clause = clause2;
  list3->clause = clause3;
  list4->clause = clause4;

  /*@ store_predata(data@pre, clist, pcnt, ccnt)
    which implies
    data@pre != 0 && Zlength(clist) == ccnt &&
    exists y,
      data_at(&(data@pre -> cnf_res), y) *
      data_at(&(data@pre -> prop_cnt), pcnt) *
      data_at(&(data@pre -> clause_cnt), ccnt) *
      sll_cnf_list(y, clist)
 */

  if (cnt == 1) {
    list1->next = data->cnf_res;
    data->cnf_res = list1;
    data->clause_cnt += 1;
    free_int_array(clause2);
    free_int_array(clause3);
    free_int_array(clause4);
    free_cnf_list(list2);
    free_cnf_list(list3);
    free_cnf_list(list4);
  } else if (cnt == 2) {
    list1->next = list2;
    list2->next = data->cnf_res;
    data->cnf_res = list1;
    data->clause_cnt += 2;
    free_int_array(clause3);
    free_int_array(clause4);
    free_cnf_list(list3);
    free_cnf_list(list4);
  } else if (cnt == 3) {
    list1->next = list2;
    list2->next = list3;
    list3->next = data->cnf_res;
    data->cnf_res = list1;
    data->clause_cnt += 3;
    free_int_array(clause4);
    free_cnf_list(list4);
  } else {
    list1->next = list2;
    list2->next = list3;
    list3->next = list4;
    list4->next = data->cnf_res;
    data->cnf_res = list1;
    data->clause_cnt += 4;
  }
}

int prop2cnf(SmtProp *p, PreData *data)
/*@ With prop clist pcnt ccnt
      Require prop_cnt_inf_SmtProp(prop) <= pcnt &&
              SmtProp_size(prop) <= 10000 &&
              Zlength(clist) <= 40000 - 4 * SmtProp_size(prop) &&
              pcnt <= 40000 - SmtProp_size(prop) &&
              store_SmtProp(p, prop) *
              store_predata(data, clist, pcnt, ccnt)
      Ensure exists clist' pcnt' ccnt' res,
             make_prop2cnf_ret(make_predata(clist', pcnt', ccnt'), res) ==
             prop2cnf_logic(prop, make_predata(clist, pcnt, ccnt)) &&
             __return == res && res != 0 && res <= pcnt' && -res <= pcnt' &&
             Zlength(clist') <= Zlength(clist) + 4 * SmtProp_size(prop) &&
             pcnt' <= pcnt + SmtProp_size(prop) &&
             store_SmtProp(p, prop) *
             store_predata(data, clist', pcnt', ccnt')
*/
{
  int res = 0;
  /*@ store_SmtProp(p, prop)
      which implies
      exists t,
      t == SmtPTID(prop) &&
      data_at(&(p -> type), t) *
      store_SmtProp'(p, prop)
   */
  switch (p->type) {
    case SMTB_PROP: {
      /*@ p@pre->type == SmtPTID(prop) && p@pre->type == 5 && p == p@pre &&
          store_SmtProp'(p, prop)
          which implies
          exists op lt rt y z,
          prop == SmtB(op, lt, rt) && p@pre != 0 &&
          data_at(&(p -> prop.Binary_prop.op), SmtPBID(op)) *
          data_at(&(p -> prop.Binary_prop.prop1), y) *
          data_at(&(p -> prop.Binary_prop.prop2), z) *
          store_SmtProp(y, lt) *
          store_SmtProp(z, rt) *
          data_at(&(p -> type), SmtPTID(prop))
       */
      /*@ Given op lt rt y z
       */
      /*@ prop_cnt_inf_SmtProp(prop) <= pcnt && prop == SmtB(op, lt, rt)
          which implies
          prop_cnt_inf_SmtProp(lt) <= pcnt &&
          prop_cnt_inf_SmtProp(rt) <= pcnt
       */
      /*@ SmtProp_size(prop) <= 10000 && prop == SmtB(op, lt, rt)
          which implies
          SmtProp_size(lt) <= 10000 &&
          SmtProp_size(rt) <= 10000
       */
      /*@ Zlength(clist) <= 40000 - 4 * SmtProp_size(prop) && prop == SmtB(op,
                                                              lt, rt)
          which implies
          Zlength(clist) <= 40000 - 4 * SmtProp_size(lt)
       */
      /*@ pcnt <= 40000 - SmtProp_size(prop) &&
          prop == SmtB(op, lt, rt)
          which implies
          pcnt <= 40000 - SmtProp_size(lt)
       */
      int p1 = prop2cnf(p->prop.Binary_prop.prop1, data);
      /*@ Assert
          exists ccnt' pcnt' clist' t,
          make_prop2cnf_ret(make_predata(clist', pcnt', ccnt'),
          p1)
          == prop2cnf_logic(lt, make_predata(clist, pcnt, ccnt))
          && p1 != 0 && p1 <= pcnt' && -p1 <= pcnt' &&
          SmtProp_size(lt) <= 10000 &&
          Zlength(clist') <= Zlength(clist) + 4 * SmtProp_size(lt) &&
          pcnt' <= pcnt + SmtProp_size(lt) &&
          pcnt <= 40000 - SmtProp_size(lt) &&
          Zlength(clist) <= 40000 - 4 * SmtProp_size(lt) &&
          SmtProp_size(lt) <= 10000 &&
          SmtProp_size(rt) <= 10000 &&
          prop_cnt_inf_SmtProp(lt) <= pcnt &&
          prop_cnt_inf_SmtProp(rt) <= pcnt &&
          prop == SmtB(op, lt, rt) &&
          p@pre != 0 &&
          t == SmtPTID(prop) &&
          prop_cnt_inf_SmtProp(prop) <= pcnt &&
          SmtProp_size(prop) <= 10000 &&
          Zlength(clist) <= 40000 - 4 * SmtProp_size(prop) &&
          pcnt <= 40000 - SmtProp_size(prop) &&
          t == 5 &&
          store_SmtProp(p@pre->prop.Binary_prop.prop1, lt) *
          store_predata(data@pre, clist', pcnt', ccnt') *
          (p == p@pre) *
          (p@pre->prop.Binary_prop.op == SmtPBID(op)) *
          store_SmtProp(p@pre->prop.Binary_prop.prop2, rt) *
          (p@pre->type == SmtPTID(prop)) *
          (res == 0) *
          (data == data@pre)
      */
      /*@ Given ccnt' pcnt' clist'
       */
      /*@ Zlength(clist') <= Zlength(clist) + 4 * SmtProp_size(lt) &&
          Zlength(clist) <= 40000 - 4 * SmtProp_size(prop) &&
          prop == SmtB(op, lt, rt)
          which implies
          Zlength(clist') <= 40000 - 4 * SmtProp_size(rt)
       */
      /*@ make_prop2cnf_ret(make_predata(clist', pcnt', ccnt'), p1)
                  == prop2cnf_logic(lt, make_predata(clist, pcnt, ccnt)) &&
          prop_cnt_inf_SmtProp(rt) <= pcnt
          which implies
          pcnt <= pcnt' &&
          prop_cnt_inf_SmtProp(rt) <= pcnt' &&
          make_prop2cnf_ret(make_predata(clist', pcnt', ccnt'), p1)
                  == prop2cnf_logic(lt, make_predata(clist, pcnt, ccnt)) &&
          prop_cnt_inf_SmtProp(rt) <= pcnt
       */
      /*@ pcnt' <= pcnt + SmtProp_size(lt) &&
          pcnt <= 40000 - SmtProp_size(prop) &&
          prop == SmtB(op, lt, rt)
          which implies
          pcnt' <= 39999 - SmtProp_size(rt)
       */
      int p2 = prop2cnf(p->prop.Binary_prop.prop2, data);
      /*@ Assert
          exists ccnt'_2 pcnt'_2 clist'_2 rt' clist'_1 pcnt'_1 ccnt'_1
                 lt' op' t',
          make_prop2cnf_ret(make_predata(clist'_2, pcnt'_2, ccnt'_2),
                            p2)
                                   == prop2cnf_logic(rt', make_predata(clist'_1,
                                             pcnt'_1, ccnt'_1))
          && p2 != 0 && p2 <= pcnt'_2
          && -p2 <= pcnt'_2 &&
          Zlength(clist'_2) <= Zlength(clist'_1) + 4 * SmtProp_size(rt')
          && pcnt'_2 <= pcnt'_1 + SmtProp_size(rt')
          && pcnt <= pcnt'_1 && prop_cnt_inf_SmtProp(rt') <= pcnt'_1 &&
          make_prop2cnf_ret(make_predata(clist'_1, pcnt'_1, ccnt'_1), p1)
                           == prop2cnf_logic(lt', make_predata(clist, pcnt,
                                             ccnt))
          && p1 != 0 && p1 <= pcnt'_1 && -p1 <= pcnt'_1 &&
          Zlength(clist'_1) <= Zlength(clist) + 4 * SmtProp_size(lt') &&
          pcnt'_1 <= pcnt + SmtProp_size(lt') &&
          prop_cnt_inf_SmtProp(lt') <= pcnt &&
          prop_cnt_inf_SmtProp(rt') <= pcnt &&
          prop == SmtB(op', lt', rt') &&
          p@pre != 0 &&
          t' == SmtPTID(prop) &&
          prop_cnt_inf_SmtProp(prop) <= pcnt &&
          SmtProp_size(prop) <= 10000 &&
          Zlength(clist) <= 40000 - 4 * SmtProp_size(prop) &&
          pcnt <= 40000 - SmtProp_size(prop) &&
          t' == 5 &&
          store_SmtProp(p@pre->prop.Binary_prop.prop2, rt') *
          store_predata(data@pre, clist'_2, pcnt'_2, ccnt'_2) *
          store_SmtProp(p@pre->prop.Binary_prop.prop1, lt') *
          (p == p@pre) *
          (p@pre->prop.Binary_prop.op == SmtPBID(op')) *
          (p@pre->type == SmtPTID(prop)) *
          (res == 0) *
          (data == data@pre)
      */
      /*@ Given ccnt'_2 pcnt'_2 clist'_2 rt' clist'_1 pcnt'_1 ccnt'_1
                lt' op' t'
       */
      /*@ store_predata(data@pre, clist'_2, pcnt'_2, ccnt'_2)
          which implies
          data@pre != 0 && Zlength(clist'_2) == ccnt'_2 &&
          prop_cnt_inf(clist'_2) <= pcnt'_2 && pcnt'_2 >= 0 &&
          exists y'',
            data_at(&(data@pre -> cnf_res), y'') *
            data_at(&(data@pre -> prop_cnt), pcnt'_2) *
            data_at(&(data@pre -> clause_cnt), ccnt'_2) *
            sll_cnf_list(y'', clist'_2)
       */
      /*@ pcnt'_2 <= pcnt'_1 + SmtProp_size(rt') &&
          pcnt'_1 <= pcnt + SmtProp_size(lt') &&
          pcnt <= 40000 - SmtProp_size(prop) &&
          prop == SmtB(op', lt', rt')
          which implies
          pcnt'_2 <= pcnt + SmtProp_size(prop) - 1 &&
          pcnt'_2 <= 39999
       */
      data->prop_cnt = data->prop_cnt + 1;
      res = data->prop_cnt;
      /*@ pcnt'_2 >= 0 && res == pcnt'_2 + 1
          which implies
          res != 0
      */
      /*@ data@pre != 0 && Zlength(clist'_2) == ccnt'_2 &&
          prop_cnt_inf(clist'_2) <= pcnt'_2 &&
          exists y'',
            data_at(&(data@pre -> cnf_res), y'') *
            data_at(&(data@pre -> prop_cnt), pcnt'_2 + 1) *
            data_at(&(data@pre -> clause_cnt), ccnt'_2) *
            sll_cnf_list(y'', clist'_2)
          which implies
          store_predata(data@pre, clist'_2, pcnt'_2 + 1, ccnt'_2)
      */
      /*@ prop_cnt_inf(clist'_2) <= pcnt'_2
          which implies
          prop_cnt_inf(clist'_2) + 1 <= pcnt'_2 + 1
       */
      /*@ Zlength(clist'_2) <= Zlength(clist'_1) + 4 * SmtProp_size(rt') &&
          Zlength(clist'_1) <= Zlength(clist) + 4 * SmtProp_size(lt') &&
          prop == SmtB(op', lt', rt')
          which implies
          Zlength(clist'_2) <= Zlength(clist) + 4 * SmtProp_size(prop) - 4
       */
      /*@ SmtProp_size(prop) <= 10000
          which implies
          4 * SmtProp_size(prop) - 4 <= 39996
       */
      clause_gen_binary(
          p1, p2, res, p->prop.Binary_prop.op,
          data) /*@ where clist = clist'_2, pcnt = (pcnt'_2 + 1),
                   ccnt = ccnt'_2, bop = op', max_size = (Zlength(clist) + 4 *
                   SmtProp_size(prop) - 4) */
          ;
      break;
    }
    case SMTU_PROP: {
      /*@ p@pre->type == SmtPTID(prop) && p@pre->type == 6 && p == p@pre &&
          store_SmtProp'(p, prop)
          which implies
          exists op sub_prop y,
          prop == SmtU(op, sub_prop) && p@pre != 0 &&
          data_at(&(p -> prop.Unary_prop.op), SmtPUID(op)) *
          data_at(&(p -> prop.Unary_prop.prop1), y) *
          store_SmtProp(y, sub_prop) *
          data_at(&(p -> type), SmtPTID(prop))
      */
      /*@ Given op sub_prop y
       */
      /*@ prop_cnt_inf_SmtProp(prop) <= pcnt && prop == SmtU(op, sub_prop)
          which implies
          prop_cnt_inf_SmtProp(sub_prop) <= pcnt
        */
      /*@ SmtProp_size(prop) <= 10000 && prop == SmtU(op, sub_prop)
          which implies
          SmtProp_size(sub_prop) <= 10000
       */
      /*@ Zlength(clist) <= 40000 - 4 * SmtProp_size(prop) && prop == SmtU(op,
                                                              sub_prop)
          which implies
          Zlength(clist) <= 40000 - 4 * SmtProp_size(sub_prop)
       */
      /*@ pcnt <= 40000 - SmtProp_size(prop) &&
          prop == SmtU(op, sub_prop)
          which implies
          pcnt <= 40000 - SmtProp_size(sub_prop)
       */
      int p1 = prop2cnf(p->prop.Unary_prop.prop1,
                        data) /* where prop = sub_prop, clist = clist, pcnt =
                                 pcnt, ccnt = ccnt */
          ;
      /*@ Assert
          exists ccnt' pcnt' clist' sub_prop' op' t',
          make_prop2cnf_ret(make_predata(clist', pcnt', ccnt'), p1)
          == prop2cnf_logic(sub_prop', make_predata(clist, pcnt, ccnt))
          && p1 != 0 && p1 <= pcnt' && -p1 <= pcnt'
          && Zlength(clist') <= Zlength(clist) + 4 * SmtProp_size(sub_prop') &&
          pcnt' <= pcnt + SmtProp_size(sub_prop') &&
          prop_cnt_inf_SmtProp(sub_prop') <= pcnt &&
          prop == SmtU(op', sub_prop') &&
          p@pre != 0 && t' == SmtPTID(prop) &&
          prop_cnt_inf_SmtProp(prop) <= pcnt &&
          SmtProp_size(prop) <= 10000 &&
          Zlength(clist) <= 40000 - 4 * SmtProp_size(prop) &&
          pcnt <= 40000 - SmtProp_size(prop) &&
          t' != 5 &&
          t' == 6 &&
          store_SmtProp(p@pre->prop.Unary_prop.prop1, sub_prop') *
          store_predata(data@pre, clist', pcnt', ccnt') *
          (p == p@pre) *
          (p@pre->prop.Unary_prop.op == SmtPUID(op')) *
          (p@pre->type == SmtPTID(prop)) *
          (res == 0) *
          (data == data@pre)
       */
      /*@ Given ccnt' pcnt' clist' sub_prop' op' t'
       */
      /*@ store_predata(data@pre, clist', pcnt', ccnt')
          which implies
          data@pre != 0 && Zlength(clist') == ccnt' &&
          prop_cnt_inf(clist') <= pcnt' && pcnt' >= 0 &&
          exists y'',
            data_at(&(data@pre -> cnf_res), y'') *
            data_at(&(data@pre -> prop_cnt), pcnt') *
            data_at(&(data@pre -> clause_cnt), ccnt') *
            sll_cnf_list(y'', clist')
       */
      /*@ pcnt' <= pcnt + SmtProp_size(sub_prop') &&
          pcnt <= 40000 - SmtProp_size(prop) &&
          prop == SmtU(op', sub_prop')
          which implies
          pcnt' <= pcnt + SmtProp_size(prop) - 1 &&
          pcnt' <= 39999
       */
      data->prop_cnt = data->prop_cnt + 1;
      res = data->prop_cnt;
      /*@ pcnt' >= 0 && res == pcnt' + 1
          which implies
          res != 0
      */
      /*@ data@pre != 0 && Zlength(clist') == ccnt' &&
           prop_cnt_inf(clist') <= pcnt' &&
           exists y'',
             data_at(&(data@pre -> cnf_res), y'') *
             data_at(&(data@pre -> prop_cnt), pcnt' + 1) *
             data_at(&(data@pre -> clause_cnt), ccnt') *
             sll_cnf_list(y'', clist')
           which implies
           store_predata(data@pre, clist', pcnt' + 1, ccnt')
       */
      /*@ prop_cnt_inf(clist') <= pcnt'
          which implies
          prop_cnt_inf(clist') + 1 <= pcnt' + 1
       */
      /*@ Zlength(clist') <= Zlength(clist) + 4 * SmtProp_size(sub_prop') &&
          prop == SmtU(op', sub_prop')
          which implies
          Zlength(clist') <= Zlength(clist) + 4 * SmtProp_size(prop) - 4
       */
      /*@ SmtProp_size(prop) <= 10000
          which implies
          4 * SmtProp_size(prop) - 4 <= 39996
       */
      clause_gen_unary(p1, res, data) /*@ where clist = clist', pcnt =
       (pcnt' + 1), ccnt = ccnt', max_size = (Zlength(clist) + 4
       * SmtProp_size(prop) - 4) */
          ;
      break;
    }
    case SMT_PROPVAR: {
      /*@ p@pre->type == 7 &&
          p@pre->type == SmtPTID(prop) && p == p@pre &&
          store_SmtProp'(p, prop)
          which implies
          exists var,
          prop == SmtV(var) && var != 0 && p@pre != 0 &&
          data_at(&(p -> prop.Propvar), var) *
          data_at(&(p -> type), SmtPTID(prop))
       */
      res = p->prop.Propvar;
      break;
    }
    default: {
      // unreachable
      /*@ Branch clear all
       */
    }
  }
  return res;
}