---
rg: 2
id: weyl-algebra-blocks-a-universal-leavitt-host-citation
kind: route
title: Import the Bilich-Hazrat-Nam non-embedding theorem
target: weyl-algebra-blocks-a-universal-leavitt-host
requires: []
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Citation import.  Bilich--Hazrat--Nam, arXiv:2512.09241v2, read from source
2026-08-17; the quotation is in
`research/artifacts/boone-higman-audit-2026-08-17.md` §A.1.

Not reproved here and no Lean counterpart exists.  This repository formalizes
`LeavittSimplicity` and `FinitePresentation` for `L_K(1,2)` but proves
nothing about which algebras embed in it, so the non-embedding is imported
whole.

## Robustness of the use made of it

Only the negative half is load-bearing, and only in its weakest form: it is
enough that *some* finitely presented `K`-algebra fails to embed, which is
what defeats a universal-host claim.  The specific mechanism — that the
Heisenberg relation is unrealizable in any Steinberg algebra — is stronger
than the graph needs, and the positive results of the same paper are not used
by any node.

Were the Weyl-algebra statement withdrawn, the dead route
`boone-higman-via-universal-leavitt-host` would revert to open rather than
to established: nobody has proved the universal host exists either, so the
route would be an unproved conjecture rather than a refuted one.
