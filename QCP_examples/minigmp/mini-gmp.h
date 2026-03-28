/*@ 
  Extern Coq (Zabs : Z -> Z) 
             (Z::max : Z -> Z -> Z)
             (Z::pow : Z -> Z -> Z)
             (mpd_store_Z : Z -> Z -> Z -> Z -> Assertion)
             (mpd_store_Z_compact: Z -> Z -> Z -> Z -> Assertion)
             (mpd_store_list : list Z -> Z -> Assertion)
             (store_Z: Z -> Z -> Assertion)
             (list_to_Z : Z -> list Z -> Z)
             (list_within_bound: Z -> list Z -> Prop)
             (last: list Z -> Z -> Z)
             (UINT_MOD: Z)
*/

/*@ Import Coq Require Import GmpAux GmpNumber */
/*@ Import Coq Import Aux */

typedef struct __mpz_struct
{
  int _mp_alloc;		/* Number of *limbs* allocated and pointed
				   to by the _mp_d field.  */
  int _mp_size;			/* abs(_mp_size) is the number of limbs the
				   last field points to.  If _mp_size is
				   negative this is a negative number.  */
  unsigned int *_mp_d;		/* Pointer to the limbs.  */
} __mpz_struct;

/* mpz_t is an array type that contains a single element of __mpz_struct, acting as a reference. */
typedef __mpz_struct mpz_t[1];
typedef __mpz_struct *mpz_ptr;
typedef const __mpz_struct *mpz_srcptr;

/* BEGIN Given Functions */

/* Swap functions. */
void int_swap(int *x, int *y)
/*@
  With
    px py
  Require
    *x == px && *y == py
  Ensure
    *x@pre == py && *y@pre == px
*/
;

void mp_ptr_swap(unsigned int **x, unsigned int **y)
/*@
  With
    px py
  Require
    *x == px && *y == py
  Ensure
    *x@pre == py && *y@pre == px
*/
;

void mpz_srcptr_swap(mpz_srcptr *x, mpz_srcptr *y)
/*@
  With
    px py
  Require
    *x == px && *y == py
  Ensure
    *x@pre == py && *y@pre == px
*/
;

/* Memory allocation functions. */
static unsigned int *
gmp_alloc_limbs (int size)
/*@
  Require
    size >= 0
  Ensure
    UIntArray::undef_full(__return, size)
*/;

static unsigned int *
gmp_realloc_limbs (unsigned int *old, int old_size, int size)
/*@
  With
    len n
  Require
    old_size >= 0 && size >= old_size &&
    mpd_store_Z_compact(UINT_MOD, old, n, len) *
    UIntArray::undef_ceil(old, len, old_size)
  Ensure
    mpd_store_Z_compact(UINT_MOD,__return, n, len) *
    UIntArray::undef_ceil(__return, len, size)
*/;

static void
gmp_free_limbs (unsigned int *old, int size)
/*@
  With
    n len
  Require
    mpd_store_Z_compact(UINT_MOD,old, n, len) *
    UIntArray::undef_ceil(old, len, size)
  Ensure
    emp
*/
;

/* END Given Functions  */

void mpn_copyi (unsigned int *d, unsigned int *s, int n);

int mpn_cmp (unsigned int *ap, unsigned int *bp, int n);

unsigned int mpn_add_1 (unsigned int *rp, unsigned int *ap, int n, unsigned int b);
unsigned int mpn_add_n (unsigned int *rp, unsigned int *ap, unsigned int *bp, int n);
unsigned int mpn_add (unsigned int *rp, unsigned int *ap, int an, unsigned int *bp, int bn);

unsigned int mpn_sub_1 (unsigned int *, unsigned int *, int, unsigned int);
unsigned int mpn_sub_n (unsigned int *, unsigned int *, unsigned int *, int);
unsigned int mpn_sub (unsigned int *, unsigned int *, int, unsigned int *, int);

void mpz_clear (mpz_t r);

int mpz_sgn (const mpz_t u);

void mpz_neg (mpz_t, const mpz_t);
void mpz_swap (mpz_t u, mpz_t v);

void mpz_add (mpz_t, const mpz_t, const mpz_t);
void mpz_sub (mpz_t, const mpz_t, const mpz_t);

void mpz_set (mpz_t, const mpz_t);