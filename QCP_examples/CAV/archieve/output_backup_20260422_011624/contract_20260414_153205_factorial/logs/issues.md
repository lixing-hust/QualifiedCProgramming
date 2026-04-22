# Issues

- Existing repository file `input/factorial.c` was already present, but it contained a loop `Inv`. The annotate skill explicitly says not to add `Inv` or `Assert`, so the final output removes that verification-stage annotation while preserving the function body and top-level contract.
- There were no existing annotate examples under this `leetcode` workspace to copy directly. I used `doc/ANNOTATE.md` plus repository examples to confirm the expected annotation syntax.
- Search did not surface a local Coq definition file for `factorial`, but `doc/ANNOTATE.md` explicitly lists factorial as the kind of simple integer semantic that should use direct `Extern Coq`. I followed that documented convention and did not create `input/factorial.v`.
- Because the task is scalar-only, aliasing, nullability, and length constraints are not applicable. This is recorded here so the absence of such clauses is deliberate rather than omitted by mistake.
