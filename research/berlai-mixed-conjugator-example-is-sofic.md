---
rg: 2
id: berlai-mixed-conjugator-example-is-sofic
kind: claim
title: The mixed-conjugator example in Berlai's introduction is sofic
distinct_from:
  berlai-nonresidual-one-relator-families-sofic: That is Berlai's published pair of families; this is the asymmetric example explicitly left as a question in that paper.
  one-relator-groups-sofic: This concerns one explicit presentation; that asks for a universal theorem.
artifacts:
  - research/artifacts/mixed-conjugator-one-relator-proof-2026-09-07.md
---

With `x^y=y^(-1)xy`, the group

    <a,b | a^(a^(b^(-1)ab^2)) = a^2>

is sofic. More generally, the same conclusion holds with `a^l` and `a^k`
in place of `a` and `a^2`, for all `l,k != 0`.

The specific `l=1,k=2` question appears in the introduction of
[Berlai, arXiv:2502.05064v1](https://arxiv.org/html/2502.05064v1).
The conclusion here follows from the accompanying written construction;
it is not attributed to Berlai and is not claimed Lean-verified.
