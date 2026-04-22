# Contract issues: string_to_lower_ascii

No unresolved contract issues.

Notes:

- The source interface is already verification-friendly: one mutable C string
  input and no return value.
- The implementation was rewritten only at the loop/character-literal surface:
  `while (s[i] != '\0')` became an explicit `while (1)` plus `s[i] == 0`
  break, and ASCII character constants became integer codes.
- The precondition explicitly excludes embedded `0` bytes in the logical
  prefix so the loop endpoint matches the modeled terminator.
