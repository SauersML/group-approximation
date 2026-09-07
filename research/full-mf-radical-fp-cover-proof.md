---
rg: 2
id: full-mf-radical-fp-cover-proof
kind: route
title: The linear inequality holds verbatim in the group presented by its own relators
target: full-mf-radical-has-fp-cover-same-generators
requires:
  - full-mf-radical-linear-relator-inequality
artifacts:
  - research/artifacts/mf-radical-linear-certificate-2026-09-07.md
---

## Proof

Each `r_j` is a relation of `G`, so the identity map on generators extends to
a surjection `P ->> G`.

Each `r_j` is a defining relator of `P`, so it is a relation of `P`.  The
inequality `(LIN)` quantifies over all dimensions and all unitary tuples and
mentions `G` only through the words `r_j`, so it holds for `P` with the same
list and the same constant.  The converse half of
`full-mf-radical-linear-relator-inequality`, applied to `P`, gives
`Res_MF(P)=P`.
