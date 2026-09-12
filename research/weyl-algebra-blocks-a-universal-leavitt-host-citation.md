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

**Hypothesis (added 2026-09-12).** The source's Theorems 3.5 and 3.7 assume `k`
has characteristic zero, from the v2 PDF text. The abstract omits this. The
import is scoped accordingly. In characteristic `p` the Heisenberg relation is
realized in `M_p(F_p) ⊆ L_{F_p}(1,2)`, so nothing here applies over `F_2`.

The dead route `boone-higman-via-universal-leavitt-host` does not rest on this
import alone. In every characteristic it is also invalidated by
`fixed-leavitt-hosts-cannot-be-universal-bh-containers`. Withdrawing or
narrowing the Weyl statement cannot make it fire.
