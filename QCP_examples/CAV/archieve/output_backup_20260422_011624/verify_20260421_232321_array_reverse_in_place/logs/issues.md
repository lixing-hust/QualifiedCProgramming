## 2026-04-21 23:44 CST

- Missing loop invariant: the input C had the function contract but no
  invariant for the `while (left < right)` loop.  Added an invariant over
  `left`, `right`, unchanged `n`/`a`, and an `IntArray::full` list
  decomposition:
  `rev(sublist(right + 1, n, l)) ++ sublist(left, right + 1, l) ++ rev(sublist(0, left, l))`.
- Logic path mismatch on the first symbolic-execution run: generated files
  initially used a path under `SimpleC.EE.CAV.output...`, while the compile
  workflow expects the stable workspace path
  `SimpleC.EE.CAV.verify_20260421_232321_array_reverse_in_place`.  Cleaned
  the generated `.v` files and reran symbolic execution with the stable
  logic path.
- Wrong compile working directory: running `coqc` from
  `/home/yangfp/QualifiedCProgramming` produced missing path errors such as
  `Cannot find physical path ... int_auto with prefix AUXLib`.  Compiling
  from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the
  documented `-R` mappings fixed the load path.
- Manual proof list normalization: generated entailments left list-equality
  obligations involving `sublist`, `replace_Znth`, append associativity, and
  simple arithmetic variants such as `right - 1 + 1`.  Added local helper
  lemmas for the swap step and loop-exit list equality, then normalized the
  residual arithmetic/list shapes in each witness proof.
