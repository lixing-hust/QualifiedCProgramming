# HumanEval Spec Logic Rewrite Progress

Created: 2026-07-09

Scope: `IntClaude`, `IntArrayClaude`, `StringClaude`, and `multi_dimensional_arrays` cases whose corresponding `QCP_examples/humaneval/spec/XX.v` currently contains a local `Fixpoint`, local `Inductive`, or `let fix`.

Goal: rewrite each target spec into a pure logical predicate style, while still allowing Coq standard-library recursive functions such as `map`, `filter`, `fold_left`, `Permutation`, `Sorted`, `Forall`, `Exists`, and string/list library helpers. After the spec rewrite, each case must be reverified from the new spec without using old proof scripts or old per-case proof history as a shortcut.

Status values:

- `todo`: not started.
- `in_progress`: currently being rewritten or verified.
- `blocked`: stopped on a semantic mismatch, missing shared infrastructure, or user decision point.
- `done`: stage passed.
- `n/a`: stage does not apply.

Per-case completion requirements:

- `spec/XX.v` loads with `opam exec --switch=coq8201 -- coqtop -quiet -l QCP_examples/humaneval/spec/XX.v`.
- `spec/XX.v` has no local `Fixpoint`, `Inductive`, or `let fix` occurrences for the target spec.
- Reverification starts from the rewritten spec and does not reuse old proof scripts as proof guidance.
- Generated files are refreshed by `symexec`; `C_XX_goal.v`, `C_XX_proof_auto.v`, and `C_XX_goal_check.v` are not edited manually.
- Final compile chain passes through `C_XX_goal_check.v`.
- Scans of `coins_XX.v`, `C_XX_proof_manual.v`, and `C_XX_goal_check.v` find no `Admitted.`, `Abort.`, `Show.`, or new `Axiom`.
- `QCP_examples/humaneval/ledger.md` contains the new rewrite/reverification cost row, including backup-derived symexec counters when backups exist.

## Summary

| Suite | Cases | Spec rewrite done | Reverification done | Blocked |
| --- | ---: | ---: | ---: | ---: |
| `IntClaude` | 4 | 4 | 0 | 0 |
| `IntArrayClaude` | 20 | 20 | 0 | 0 |
| `StringClaude` | 27 | 23 | 1 | 4 |
| `multi_dimensional_arrays` | 7 | 5 | 0 | 2 |
| **Total** | **58** | **52** | **1** | **6** |

## Progress Table

| Suite | Case | Spec | Current recursive form | Rewrite idea | Spec rewrite | Spec load check | Reverification | Ledger row | Notes |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `IntClaude` | `C_36` | `spec/36.v` | `Fixpoint` | finite digit-position enumeration | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntClaude` | `C_39` | `spec/39.v` | `Fixpoint` | `Nat.iter` Fibonacci state | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntClaude` | `C_131` | `spec/131.v` | `Fixpoint` | finite digit-position enumeration and `fold_left` product | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntClaude` | `C_139` | `spec/139.v` | `Fixpoint` | factorial as finite product over `seq` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_46` | `spec/46.v` | `Fixpoint` | `Nat.iter` four-value Fib4 state | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_55` | `spec/55.v` | `Fixpoint` | `Nat.iter` Fibonacci state | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_63` | `spec/63.v` | `Fixpoint` | `Nat.iter` three-value FibFib state | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_69` | `spec/69.v` | `Fixpoint` | frequency via `filter`, max via `fold_left` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_70` | `spec/70.v` | `Fixpoint` | alternating remaining min/max by occurrence counts | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_73` | `spec/73.v` | `Fixpoint` | pairwise half comparison via `combine`/`filter` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_85` | `spec/85.v` | `Fixpoint` | indexed sum via `combine` and `fold_left` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_94` | `spec/94.v` | `Fixpoint` | finite digit-position sum | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_104` | `spec/104.v` | `Fixpoint` | filtered list plus `Permutation`/`Sorted` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_107` | `spec/107.v` | `Fixpoint` | palindrome counts over finite `seq` range | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_108` | `spec/108.v` | `Fixpoint` | signed digit sum by finite digit positions | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_109` | `spec/109.v` | `Fixpoint` | existence of sorted cyclic rotation | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_116` | `spec/116.v` | `Fixpoint` | `Permutation`/`Sorted` under bit-count order | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_121` | `spec/121.v` | `Fixpoint` | indexed sum via `combine` and `fold_left` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_123` | `spec/123.v` | `Fixpoint` | Collatz adjacent-step relation over `combine l (tl l)` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_130` | `spec/130.v` | `Fixpoint` | closed finite sum for odd terms | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_142` | `spec/142.v` | `Fixpoint` | indexed transform via `combine` and `fold_left` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_145` | `spec/145.v` | `Fixpoint` | stable sorted indexed output relation | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_146` | `spec/146.v` | `Fixpoint` | most-significant digit via finite fold | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `IntArrayClaude` | `C_155` | `spec/155.v` | `Fixpoint` | even/odd digit counts over finite digit positions | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_6` | `spec/6.v` | `Fixpoint` | blocked: space-splitting/max-depth scan needs a relation that preserves multi-space behavior | blocked | n/a | todo | todo | Still contains recursion; left unchanged to avoid changing whitespace semantics. |
| `StringClaude` | `C_15` | `spec/15.v` | `let fix`, `Fixpoint` | decimal `string_of_nat` over digit positions; sequence via `String.concat` | done | done | done | done | Worked only in `spec_logic_rewrite_c_files`; full-chain passed against direct original `spec/15.v` wrappers in `coins_15.v`. Compiled `coins_15.v`, `C_15_goal.v`, `C_15_proof_auto.v`, `C_15_proof_manual.v`, and `C_15_goal_check.v`; scans of `coins_15.v`, `C_15_proof_manual.v`, and `C_15_goal_check.v` found no `Admitted.`, `Abort.`, `Show.`, or `Axiom`. Ledger row includes backup-derived counters: first_vc=4, total_symexec=5, regen_after_first=1. |
| `StringClaude` | `C_17` | `spec/17.v` | `Fixpoint` | blocked: music token splitting ignores repeated/leading spaces | blocked | n/a | todo | todo | Still contains recursion; needs a whitespace-preserving split relation. |
| `StringClaude` | `C_19` | `spec/19.v` | `Inductive` | numeral lookup as `word_to_num : string -> option nat` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_50` | `spec/50.v` | `Fixpoint` | lowercase precondition via `Forall` over `list_ascii_of_string` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_51` | `spec/51.v` | `Fixpoint` | string filtering via list/string conversions | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_56` | `spec/56.v` | `Fixpoint` | bracket balance via `fold_left` optional depth | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_61` | `spec/61.v` | `Fixpoint` | parenthesis balance via `fold_left` optional depth | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_64` | `spec/64.v` | `Fixpoint` | vowel count via `filter`; terminal y/Y via `rev` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_65` | `spec/65.v` | `Fixpoint` | decimal digits by position; output via `String.concat` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_66` | `spec/66.v` | `Fixpoint` | uppercase ASCII sum via `filter` and `fold_left` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_67` | `spec/67.v` | `Fixpoint` | decimal parsing via `fold_left` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_78` | `spec/78.v` | `Fixpoint` | prime-hex count via `filter` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_79` | `spec/79.v` | `Fixpoint` | binary string from finite bit-position enumeration | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_84` | `spec/84.v` | `Fixpoint` | digit sum and binary string via finite positions | done | done | todo | todo | `coqtop` passed with existing large-number warning; recursive keyword scan clean. |
| `StringClaude` | `C_86` | `spec/86.v` | `Fixpoint` | blocked: per-word char sorting must preserve exact blank spaces | blocked | n/a | todo | todo | Still contains recursion; needs a word-segment relation that preserves blank-space layout. |
| `StringClaude` | `C_89` | `spec/89.v` | `Fixpoint` | lowercase precondition via `Forall` over `list_ascii_of_string` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_91` | `spec/91.v` | `Fixpoint` | boredom scan via `fold_left` state | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_103` | `spec/103.v` | `Fixpoint` | binary string from finite bit-position enumeration | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_118` | `spec/118.v` | `let fix` | letter-only precondition via `Forall is_alpha` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_119` | `spec/119.v` | `Fixpoint` | parenthesis balance via `fold_left` optional depth | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_132` | `spec/132.v` | `Fixpoint` | nested subsequence as four increasing indices | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_140` | `spec/140.v` | `Fixpoint` | space-run normalization via `fold_left` state | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_143` | `spec/143.v` | `Fixpoint`, `let fix` | blocked: prime-length word filtering needs whitespace-preserving split/join relation | blocked | n/a | todo | todo | Still contains recursion; direct `String.concat` rewrite would change spacing behavior. |
| `StringClaude` | `C_144` | `spec/144.v` | `Fixpoint` | fraction number parsing via `fold_left` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_154` | `spec/154.v` | `Fixpoint` | use Coq stdlib `list_ascii_of_string`; rotation/substr as existentials | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `StringClaude` | `C_161` | `spec/161.v` | `Fixpoint` | letter existence via `existsb` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `multi_dimensional_arrays` | `C_7` | `spec/7.v` | `Fixpoint` | blocked: substring filter needs stable order and duplicate-aware relation | blocked | n/a | todo | todo | Still contains recursion; should be handled like `C_29` but with substring relation. |
| `multi_dimensional_arrays` | `C_29` | `spec/29.v` | `Fixpoint` | stable prefix filter via order condition and membership iff | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `multi_dimensional_arrays` | `C_87` | `spec/87.v` | `Inductive`, `Fixpoint` | coordinate hit iff plus `Sorted coord_order` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `multi_dimensional_arrays` | `C_95` | `spec/95.v` | `Inductive` | represent key type as `option string` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `multi_dimensional_arrays` | `C_101` | `spec/101.v` | `Fixpoint` | blocked: comma/space word splitting ignores repeated delimiters | blocked | n/a | todo | todo | Still contains recursion; needs delimiter-run split relation. |
| `multi_dimensional_arrays` | `C_112` | `spec/112.v` | `Fixpoint` | deletion via `filter`; palindrome via `list_eq_dec` | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |
| `multi_dimensional_arrays` | `C_158` | `spec/158.v` | `Fixpoint` | unique chars via `nodup`; lex order via first differing char | done | done | todo | todo | `coqtop` passed; recursive keyword scan clean. |

## Commands

Refresh candidate list:

```bash
for d in QCP_examples/humaneval/IntClaude QCP_examples/humaneval/IntArrayClaude QCP_examples/humaneval/StringClaude QCP_examples/humaneval/multi_dimensional_arrays; do
  for f in "$d"/C_*.c; do
    b=$(basename "$f")
    n=${b#C_}
    n=${n%.c}
    s=QCP_examples/humaneval/spec/$n.v
    if test -f "$s" && rg -q '\b(Fixpoint|Inductive)\b|let fix' "$s"; then
      printf '%s C_%s %s\n' "$(basename "$d")" "$n" "$s"
    fi
  done
done
```

Check one rewritten spec:

```bash
opam exec --switch=coq8201 -- coqtop -quiet -l QCP_examples/humaneval/spec/XX.v
rg -n '\b(Fixpoint|Inductive)\b|let fix' QCP_examples/humaneval/spec/XX.v
```
