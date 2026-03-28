#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "mini-gmp.h"

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/
{
  return x >= 0 ? x : -x;
}

int gmp_max(int a, int b)
/*@
  Require emp
  Ensure __return == Z::max(a, b)
*/
{
  return a > b ? a : b;
}

int gmp_cmp(int a, int b)
/*@
  Require emp
  Ensure 
    emp * 
    (a > b && __return == 1 || 
    a == b && __return == 0 ||
    a < b && __return == -1)
*/
{
  return (a > b) - (a < b);
}

/* MPN interface */

/* 从 低地址向高地址 顺序复制 */
void
mpn_copyi (unsigned int *d, unsigned int *s, int n)
/*@
  With val
  Require
    mpd_store_Z(UINT_MOD, s, val, n) *
    UIntArray::undef_full(d, n)
  Ensure 
    mpd_store_Z(UINT_MOD,s, val, n) *
    mpd_store_Z(UINT_MOD,d, val, n)
*/
{
  /*@
    mpd_store_Z(UINT_MOD, s, val, n)
    which implies
    exists l,
      Zlength(l) == n && 
      list_to_Z(UINT_MOD, l) == val && list_within_bound(UINT_MOD, l) &&
      UIntArray::full(s, n, l)
  */
  /*@ Given l */
  int i;
  /*@ Inv
    0 <= i && i <= n@pre && 
    UIntArray::full(d@pre, i, sublist(0, i, l)) * 
    UIntArray::undef_ceil(d@pre, i, n@pre)
  */
  for (i = 0; i < n; i++) {
      d[i] = s[i];
  }
}

/* 大于返回1，小于返回-1，等于返回0 */
int
mpn_cmp (unsigned int *ap, unsigned int *bp, int n)
/*@
  With val1 val2
  Require
    0 <= n &&
    mpd_store_Z_compact(UINT_MOD, ap, val1, n) *
    mpd_store_Z_compact(UINT_MOD, bp, val2, n)  
  Ensure
    (val1 > val2 && __return == 1 ||
    val1 == val2 && __return == 0 ||
    val1 < val2 && __return == -1) &&
    mpd_store_Z_compact(UINT_MOD, ap, val1, n) *
    mpd_store_Z_compact(UINT_MOD, bp, val2, n)
*/
{
  /*@
    mpd_store_Z_compact(UINT_MOD, ap, val1, n) * mpd_store_Z_compact(UINT_MOD, bp, val2, n)
    which implies
    exists l1 l2,
    list_to_Z(UINT_MOD, l1) == val1 && last(l1, 1) >= 1 && list_within_bound(UINT_MOD, l1) &&
    list_to_Z(UINT_MOD, l2) == val2 && last(l2, 1) >= 1 && list_within_bound(UINT_MOD, l2) &&
    n == Zlength(l1) && n == Zlength(l2) && 
    UIntArray::full(ap, n, l1) * UIntArray::full(bp, n, l2) 
  */
  /*@
    Given l1 l2
  */
  --n;
  /*@ Inv
    -1 <= n && n < n@pre &&
    sublist(n + 1, n@pre, l1) == sublist(n + 1, n@pre, l2)
  */
  while (n >= 0)
    {
      if (ap[n] != bp[n])
	      return ap[n] > bp[n] ? 1 : -1;
      --n;
    }
  // Note: The parser cannot parse "--n" in loop condition so we paraphrased it.
  /*
  while (--n >= 0)
    {
      if (ap[n] != bp[n])
	return ap[n] > bp[n] ? 1 : -1;
    }
  */
  return 0;
}

/*处理位数不同的情况*/
static int
mpn_cmp4 (unsigned int *ap, int an, unsigned int *bp, int bn)
/*@
  With val1 val2
  Require
    an >= 0 && bn >= 0 && 
    mpd_store_Z_compact(UINT_MOD, ap, val1, an) *
    mpd_store_Z_compact(UINT_MOD, bp, val2, bn)
  Ensure
    (val1 > val2 && __return == 1 ||
    val1 == val2 && __return == 0 ||
    val1 < val2 && __return == -1) &&
    mpd_store_Z_compact(UINT_MOD, ap, val1, an) *
    mpd_store_Z_compact(UINT_MOD, bp, val2, bn)
*/
{
  if (an != bn)
    return an < bn ? -1 : 1;
  else {
    return mpn_cmp (ap, bp, an);
  }
}


/*返回非0的位数*/
static int
mpn_normalized_size (unsigned int *xp, int n)
/*@
  With val
  Require
    0 <= n && 
    mpd_store_Z(UINT_MOD, xp, val, n) 
  Ensure
    0 <= __return && __return <= n &&
    mpd_store_Z_compact(UINT_MOD, xp, val, __return) * 
    UIntArray::undef_ceil(xp, __return, n)
*/
{
  /*@
    mpd_store_Z(UINT_MOD, xp, val, n)
    which implies
    exists l,
    list_to_Z(UINT_MOD, l) == val && list_within_bound(UINT_MOD, l) && 
    Zlength(l) == n &&
    UIntArray::full(xp, n, l)
  */
  /*@ n <= INT_MAX by local */
  /*@
    Given l
  */
  /*@Inv
    n >= 0 && n <= n@pre &&
    list_to_Z(UINT_MOD, sublist(0, n, l)) == val &&
    UIntArray::full(xp@pre, n, sublist(0, n, l)) *
    UIntArray::undef_ceil(xp@pre, n, n@pre)
  */
  while (n > 0 && xp[n-1] == 0)
    --n;
  return n;
}

/* 多精度数ap 加上单精度数b，返回最后产生的进位 */
unsigned int
mpn_add_1 (unsigned int *rp, unsigned int *ap, int n, unsigned int b)
/*@
  With val
  Require
    n > 0 && 0 <= b && b <= UINT_MAX &&
    mpd_store_Z(UINT_MOD,ap, val, n) *
    UIntArray::undef_full(rp, n)
  Ensure
    exists val',
    mpd_store_Z(UINT_MOD, ap, val, n) *
    mpd_store_Z(UINT_MOD, rp, val', n) &&
    (val' + __return * Z::pow(UINT_MOD, n) == val + b)
*/
{
  /*@
    mpd_store_Z(UINT_MOD,ap, val, n)
    which implies
    exists l,
      Zlength(l) == n && 
      list_to_Z(UINT_MOD, l) == val && list_within_bound(UINT_MOD, l) &&
      UIntArray::full(ap, n, l)
  */

  /*@ Given l */
  int i;
  i = 0;
  do
  {
    unsigned int r = ap[i] + b;
    // Carry out
    b = (r < b);
    rp[i] = r;
    ++i;
  }
  /*@ Inv Assert 
    exists l' val1 val2,
    1 <= i && i <= n@pre && 0 <= b && b < UINT_MOD && n == n@pre &&
    ap == ap@pre && rp == rp@pre &&
    (val2 + b * Z::pow(UINT_MOD, i) == val1 + b@pre) &&
    Zlength(l') == i &&
    list_to_Z(UINT_MOD, sublist(0, i, l)) == val1 &&
    list_to_Z(UINT_MOD, l') == val2 &&
    list_within_bound(UINT_MOD, l') &&
    Zlength(l) == n && 
    list_to_Z(UINT_MOD, l) == val && list_within_bound(UINT_MOD, l) &&
    UIntArray::full(ap, n@pre, l) * 
    UIntArray::full(rp@pre, i, l') *
    UIntArray::undef_ceil(rp@pre, i, n@pre)
  */
  while (i < n);

  return b;
}

/* 位数相同的多精度数ap 加上多精度数bp，返回最后产生的进位 */
unsigned int
mpn_add_n (unsigned int *rp, unsigned int *ap, unsigned int *bp, int n)
/*@
 With val_a val_b
 Require
   n > 0 &&
   mpd_store_Z(UINT_MOD, ap, val_a, n) *
   mpd_store_Z(UINT_MOD, bp, val_b, n) *
   UIntArray::undef_full(rp, n) 
 Ensure
   exists val_r_out,
   (val_r_out + __return * Z::pow(UINT_MOD, n) == val_a + val_b) &&
   mpd_store_Z(UINT_MOD, ap, val_a, n) *
   mpd_store_Z(UINT_MOD, bp, val_b, n) *
   mpd_store_Z(UINT_MOD, rp, val_r_out, n) 
*/
{
  /*@
    mpd_store_Z(UINT_MOD, ap, val_a, n) * mpd_store_Z(UINT_MOD, bp, val_b, n)
    which implies
    exists l_a l_b,
      Zlength(l_a) == n && Zlength(l_b) == n && 
      list_to_Z(UINT_MOD, l_a) == val_a && list_within_bound(UINT_MOD, l_a) &&
      list_to_Z(UINT_MOD, l_b) == val_b && list_within_bound(UINT_MOD, l_b) &&
      UIntArray::full(ap, n, l_a) * UIntArray::full(bp, n, l_b)
  */
  int i;
  unsigned int cy;

  i = 0;
  cy = 0;
  /*@ Given l_a l_b */

  /*@Inv
    exists l_r val_a_prefix val_b_prefix val_r,
      0 <= i && i <= n@pre && 0 <= cy && cy <= UINT_MAX &&
      list_to_Z(UINT_MOD, sublist(0, i, l_a)) == val_a_prefix &&
      list_to_Z(UINT_MOD, sublist(0, i, l_b)) == val_b_prefix &&
      list_to_Z(UINT_MOD, l_r) == val_r &&
      list_within_bound(UINT_MOD, l_r) &&
      Zlength(l_r) == i &&
      (val_r + cy * Z::pow(UINT_MOD, i) == val_a_prefix + val_b_prefix) &&
      UIntArray::full(rp@pre, i, l_r) *
      UIntArray::undef_ceil(rp@pre, i, n@pre)
  */
  while (i < n)
  {
    unsigned int a, b, r;
    a = ap[i]; b = bp[i];
    r = a + cy;
    cy = (r < cy);
    r += b;
    cy += (r < b);
    rp[i] = r;
    ++i;
  }
  return cy;
}

/*不同位数的多精度数相加，返回最后的进位*/
unsigned int
mpn_add (unsigned int *rp, unsigned int *ap, int an, unsigned int *bp, int bn)
/*@
 With val_a val_b
 Require
   an >= bn && an > 0 && bn > 0 &&
   mpd_store_Z(UINT_MOD, ap, val_a, an) *
   mpd_store_Z(UINT_MOD, bp, val_b, bn) *
   UIntArray::undef_full(rp, an)
 Ensure
   exists val_r_out,
   (val_r_out + __return * Z::pow(UINT_MOD, an) == val_a + val_b) &&
   mpd_store_Z(UINT_MOD, ap, val_a, an) *
   mpd_store_Z(UINT_MOD, bp, val_b, bn) *
   mpd_store_Z(UINT_MOD, rp, val_r_out, an)
*/
{
  unsigned int cy;
  /*@
    mpd_store_Z(UINT_MOD, ap, val_a, an) && an >= bn && bn > 0
    which implies
      exists val_a_low val_a_high,
        val_a == val_a_low + val_a_high * Z::pow(UINT_MOD, bn) &&
        mpd_store_Z(UINT_MOD, ap, val_a_low, bn) *
        mpd_store_Z(UINT_MOD, ap + bn * sizeof(unsigned int), val_a_high, an - bn) 
    */
  /*@
    Given val_a_low val_a_high
   */
  /*@ an >= bn && bn > 0 && UIntArray::undef_full(rp, an)
  which implies
    UIntArray::undef_full(rp, bn) *
    UIntArray::undef_full(rp + bn * sizeof(unsigned int), an - bn)
  */
  cy = mpn_add_n (rp, ap, bp, bn) /*@ where val_a=val_a_low, val_b=val_b*/ ;
  /*@
  exists val_r_out, mpd_store_Z(UINT_MOD,rp, val_r_out, bn)
  which implies
    exists l_r,
    Zlength(l_r) == bn && 
    list_to_Z(UINT_MOD, l_r) == val_r_out && list_within_bound(UINT_MOD, l_r) &&
    UIntArray::full(rp, bn, l_r) 
  */
  /*@ 0 <= cy && cy <= UINT_MAX by local */
  if (an > bn) {
    cy = mpn_add_1 (rp + bn, ap + bn, an - bn, cy) /*@ where val=val_a_high*/;
  }
  return cy;
}

/*unsigned int
mpn_sub_1 (unsigned int *rp, unsigned int *ap, int n, unsigned int b)
{
  int i;
  //assert (n > 0);
  i = 0;
  do
    {
      unsigned int a = ap[i];
      // Carry out
      unsigned int cy = a < b;
      rp[i] = a - b;
      b = cy;
    }
  while (++i < n);

  return b;
}*/

/*unsigned int
mpn_sub_n (unsigned int *rp, unsigned int *ap, unsigned int *bp, int n)
{
  int i;
  unsigned int cy;

  for (i = 0, cy = 0; i < n; i++)
    {
      unsigned int a, b;
      a = ap[i]; b = bp[i];
      b += cy;
      cy = (b < cy);
      cy += (a < b);
      rp[i] = a - b;
    }
  return cy;
}*/

/*unsigned int
mpn_sub (unsigned int *rp, unsigned int *ap, int an, unsigned int *bp, int bn)
{
  unsigned int cy;
  //assert (an >= bn);
  cy = mpn_sub_n (rp, ap, bp, bn);
  if (an > bn)
    cy = mpn_sub_1 (rp + bn, ap + bn, an - bn, cy);
  return cy;
}*/

/* MPZ interface */

void
mpz_clear (mpz_t r)
/*@
  With
    n
  Require
    store_Z(r, n)
  Ensure
    exists size cap ptr,
      r -> _mp_size == size && r -> _mp_alloc == cap && r -> _mp_d == ptr
*/
{
  /*@
    store_Z(r, n)
    which implies
    exists ptr size cap,
      Zabs(size) <= cap &&
      (size < 0 && n < 0 && mpd_store_Z_compact(UINT_MOD,ptr, -n, -size) * UIntArray::undef_ceil(ptr, -size, cap) ||
        size >= 0 && n >= 0 && mpd_store_Z_compact(UINT_MOD,ptr, n, size) * UIntArray::undef_ceil(ptr, size, cap)) &&
      r -> _mp_size == size &&
      r -> _mp_alloc == cap &&
      r -> _mp_d == ptr
  */
  /*@ Given size */
  if (r->_mp_alloc)
    gmp_free_limbs (r->_mp_d, r->_mp_alloc) ;
}

static unsigned int *
mpz_realloc (mpz_t r, int size)
/*@
  With
    ptr old cap n
  Require
    size >= cap && size <= INT_MAX && cap >= 0 && cap <= INT_MAX &&
    Zabs(old) <= cap &&
    (old < 0 && n < 0 && mpd_store_Z_compact(UINT_MOD,ptr, -n, -old) * UIntArray::undef_ceil(ptr, -old, cap) ||
        old >= 0 && n >= 0 && mpd_store_Z_compact(UINT_MOD,ptr, n, old) * UIntArray::undef_ceil(ptr, old, cap)) &&
      r -> _mp_size == old &&
      r -> _mp_alloc == cap &&
      r -> _mp_d == ptr
  Ensure 
    (n < 0 && mpd_store_Z_compact(UINT_MOD,__return, -n, -old) * UIntArray::undef_ceil(__return, -old, Z::max(size,1)) ||
      n >= 0 && mpd_store_Z_compact(UINT_MOD,__return, n, old) * UIntArray::undef_ceil(__return, old, Z::max(size,1))) &&
    r -> _mp_size == old &&
    r -> _mp_alloc == Z::max(size,1) &&
    r -> _mp_d == __return
*/
{
  size = gmp_max (size, 1);

  if (r->_mp_alloc)
    r->_mp_d = gmp_realloc_limbs (r->_mp_d, r->_mp_alloc, size);
  else
    r->_mp_d = gmp_alloc_limbs (size);
  r->_mp_alloc = size;

  if (gmp_abs (r->_mp_size) > size)
    r->_mp_size = 0;

  return r->_mp_d;
}

/* Realloc for an mpz_t WHAT if it has less than NEEDED limbs.  */
/*unsigned int *mrz_realloc_if(mpz_t z,int n) 
{
  return n > z->_mp_alloc ? mpz_realloc(z, n) : z->_mp_d;
}*/

/* MPZ comparisons and the like. */
int
mpz_sgn (const mpz_t u)
/*@
  With
    n
  Require
    store_Z(u, n)
  Ensure
    store_Z(u, n) &&
    (n > 0 && __return == 1 || n == 0 && __return == 0 ||
      n < 0 && __return == -1)
*/
{
  /*@
    store_Z(u, n)
    which implies
    exists ptr cap size,
      Zabs(size) <= cap &&
      (size < 0 && n < 0 && mpd_store_Z_compact(UINT_MOD,ptr, -n, -size) * UIntArray::undef_ceil(ptr, -size, cap) ||
        size >= 0 && n >= 0 && mpd_store_Z_compact(UINT_MOD,ptr, n, size) * UIntArray::undef_ceil(ptr, size, cap)) &&
      u->_mp_size == size && 
      u->_mp_alloc == cap && 
      u->_mp_d == ptr
  */
  return gmp_cmp (u->_mp_size, 0);
}

void
mpz_swap (mpz_t u, mpz_t v)
/*@
  With
    n m
  Require
    store_Z(u, n) * store_Z(v, m)
  Ensure
    store_Z(u, m) * store_Z(v, n)
*/
{
  /*@
    store_Z(u, n)
    which implies
    exists ptr1 cap1 size1,
      Zabs(size1) <= cap1 &&
      (size1 < 0 && n < 0 && mpd_store_Z_compact(UINT_MOD,ptr1, -n, -size1) * UIntArray::undef_ceil(ptr1, -size1, cap1) ||
        size1 >= 0 && n >= 0 && mpd_store_Z_compact(UINT_MOD,ptr1, n, size1) * UIntArray::undef_ceil(ptr1, size1, cap1)) &&
      u->_mp_size == size1 && 
      u->_mp_alloc == cap1 && 
      u->_mp_d == ptr1
  */
  /*@
    store_Z(v, m)
    which implies
    exists ptr2 cap2 size2,
      Zabs(size2) <= cap2 &&
      (size2 < 0 && m < 0 && mpd_store_Z_compact(UINT_MOD,ptr2, -m, -size2) * UIntArray::undef_ceil(ptr2, -size2, cap2) ||
        size2 >= 0 && m >= 0 && mpd_store_Z_compact(UINT_MOD,ptr2, m, size2) * UIntArray::undef_ceil(ptr2, size2, cap2)) &&
      v->_mp_size == size2 && 
      v->_mp_alloc == cap2 && 
      v->_mp_d == ptr2
  */
  /*@
    Given ptr1 cap1 size1 ptr2 cap2 size2
  */
  int_swap (&u->_mp_alloc, &v->_mp_alloc);
  mp_ptr_swap(&u->_mp_d, &v->_mp_d);
  int_swap (&u->_mp_size, &v->_mp_size);
}

/* MPZ addition and subtraction */

/*static int
mpz_abs_add (mpz_t r, const mpz_t a, const mpz_t b)
{
  int an = gmp_abs (a->_mp_size);
  int bn = gmp_abs (b->_mp_size);
  unsigned int *rp;
  unsigned int cy;

  if (an < bn)
    {
      mpz_srcptr_swap (a, b);
      int_swap (an, bn);
    }

  rp = mrz_realloc_if (r, an + 1);
  cy = mpn_add (rp, a->_mp_d, an, b->_mp_d, bn);

  rp[an] = cy;

  return an + cy;
}*/

/*static int
mpz_abs_sub (mpz_t r, const mpz_t a, const mpz_t b)
{
  int an = gmp_abs (a->_mp_size);
  int bn = gmp_abs (b->_mp_size);
  int cmp;
  unsigned int *rp;

  cmp = mpn_cmp4 (a->_mp_d, an, b->_mp_d, bn);
  if (cmp > 0)
    {
      rp = mrz_realloc_if (r, an);
      mpn_sub (rp, a->_mp_d, an, b->_mp_d, bn);
      return mpn_normalized_size (rp, an);
    }
  else if (cmp < 0)
    {
      rp = mrz_realloc_if (r, bn);
      mpn_sub (rp, b->_mp_d, bn, a->_mp_d, an);
      return -mpn_normalized_size (rp, bn);
    }
  else
    return 0;
}*/

/*void
mpz_add (mpz_t r, const mpz_t a, const mpz_t b)
{
  int rn;

  if ( (a->_mp_size ^ b->_mp_size) >= 0)
    rn = mpz_abs_add (r, a, b);
  else
    rn = mpz_abs_sub (r, a, b);

  r->_mp_size = a->_mp_size >= 0 ? rn : - rn;
}*/

/*void
mpz_sub (mpz_t r, const mpz_t a, const mpz_t b)
{
  int rn;

  if ( (a->_mp_size ^ b->_mp_size) >= 0)
    rn = mpz_abs_sub (r, a, b);
  else
    rn = mpz_abs_add (r, a, b);

  r->_mp_size = a->_mp_size >= 0 ? rn : - rn;
}*/
