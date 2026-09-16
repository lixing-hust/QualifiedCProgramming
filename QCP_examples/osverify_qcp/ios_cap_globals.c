#include "include/ios_cap_types.h"

/* Link-time storage only; function contracts supply the initial logical state. */
CSPACE *OSCSpacePrioTbl[64];
unsigned char OSRunning;
unsigned char OSPrioCur;
unsigned char CapParent[64];
OS_TCB *OSTCBCur;
