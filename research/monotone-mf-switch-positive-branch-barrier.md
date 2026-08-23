---
rg: 2
id: monotone-mf-switch-positive-branch-barrier
kind: claim
title: A monotone append-on-halt switch cannot have an MF positive branch with a surviving mark
artifacts:
  - research/artifacts/seeded-self-aware-mf-switch-2026-08-23.md
distinct_from:
  post-candidate-nemesis-has-a-finality-dilemma: that is a temporal inconsistency for matrix-triggered moving presentations; this is a quotient-functoriality obstruction for proof-triggered recursively enumerable presentations.
  marked-mf-radical-seed-gives-proof-triggered-compiler: that constructs a valid seeded switch whose halting branch is necessarily still non-MF; this explains why no such switch can make that branch MF while preserving the mark.
---

Suppose the nonhalting presentation of a compiler is `Gamma_infty`, halting
only appends relators, and `q:Gamma_infty->Gamma_halt` is the resulting
quotient map. If

```text
w in Res_MF(Gamma_infty)
and
q(w)!=1,
```

then `Gamma_halt` is non-MF. Indeed MF-radical functoriality puts `q(w)` in
`Res_MF(Gamma_halt)`, where it remains nontrivial.

Consequently a monotone append-on-halt compiler cannot simultaneously have a
nonhalting MF-radical collapse, a surviving halting mark, and an MF halting
branch. A seed-free compiler with a genuinely positive MF branch would need
a nonmonotone architecture or a different semantic interface.
