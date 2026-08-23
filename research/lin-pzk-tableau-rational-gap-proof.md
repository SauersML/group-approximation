---
rg: 2
id: lin-pzk-tableau-rational-gap-proof
kind: route
title: Apply the finite PZK sampler to the fixed Lin loop BCS and split rational marginals
target: lin-pzk-tableau-rational-qc-not-qa-correlation
requires:
  - lin-explicit-fixed-bcs-gap-via-generic-conversion
  - pzk-tableau-private-s5-gauge-normal-form
artifacts:
  - research/artifacts/mastel-slofstra-tableau-compiler-audit-2026-08-23.md
---

Mastel--Slofstra Proposition 8.4 preserves perfect commuting strategies
through `B |-> Tab_sub(Obl(B^3SAT))`.  The commuting version of the finite
mask/randomizer construction in Proposition 8.6 is the same tensor-product
construction used for Theorem 8.8, and its two-question statistics are the
finite simulator table.  Hence `p_tab` is rational, perfect, and in `C_qc`.

Proposition 8.5 pulls defect back with a finite polynomial constant.  Applied
to the fixed positive-gap `B_loop`, it excludes quantum strategies of tableau
value tending to one.  An assumed `p_tab in C_qa` would give exactly such a
sequence (equivalently a Connes-embeddable perfect synchronous trace), proving
`(PTR1)`.

For `(PTR2)`, take a common denominator `L` of all marginal probabilities.
For each positive-marginal answer `a` to `x`, tensor its projection with a
uniform partition of size `L p_tab(a|x)`.  The resulting refined answer PVM
has `L` outcomes of trace `1/L`.  Its pair table is rational and perfect.
The deterministic map forgetting the partition coordinate takes every
finite-dimensional or Connes-embeddable refined strategy to one for the old
game, so the separation is preserved.
