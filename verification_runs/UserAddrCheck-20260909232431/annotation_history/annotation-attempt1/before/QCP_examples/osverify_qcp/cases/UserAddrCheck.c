/*
 * Faithful C transcription of:
 *   QCP_examples/osverify/certiucos/code/ifun_useraddrchk.v
 *   Definition UserAddrCheck_impl
 *
 * The legacy model uses Int32u for addr and Tint8 (documented there as
 * Int8u) for the result.  Keep the control flow and boundary constants
 * identical to that model.
 */

#define USER_ADDR_START 0U
#define USER_ADDR_END 4294867295U

unsigned char UserAddrCheck(unsigned int addr)
/*@ With (a : Z)
    Require addr == a &&
            0 <= a && a <= 4294967295 && emp
    Ensure (((a <= 0 || 4294867295 < a) && __return == 0) ||
            ((0 < a && a <= 4294867295) && __return == 1)) && emp
*/
{
    if (USER_ADDR_START >= addr || addr > USER_ADDR_END) {
        return (unsigned char)0;
    }
    return (unsigned char)1;
}
