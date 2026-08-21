---
rg: 2
id: two-sided-pauli-gauge-bridge-proof
kind: route
title: Restrict the unique Pauli spin type to its Z and X maximal abelian charts
target: two-sided-pauli-gauge-bridge-preserves-spin-scale
requires:
  - finite-schur-clifford-packet-flexible-hs-exactification
  - finite-group-shared-overlap-polar-alignment
---

The normal-form theorem for graphs of groups embeds `G_0,H,G_1` in `(TPG3)`,
so every nontrivial marked word in either packet factor survives.

Fix `J=-1` and a character `lambda` of `T`. The Pauli factor `E_k` has one
spin simple of dimension `2^k`. Its restriction to either maximal abelian
subgroup

```text
<J,Z_1,...,Z_k>,       <J,X_1,...,X_k>
```

is the multiplicity-free sum of all `2^k` marked characters. Hence an
`H`-spin multiplicity `n_lambda` contributes exactly `n_lambda` copies of
every edge character on both sides. A `G_a` packet-simple multiplicity
`m^a_(lambda,epsilon)` contributes `D m^a_(lambda,epsilon)` copies by
hypothesis. Equality of the two restrictions gives `(TPG4)`.

The approximate statement is the standard fixed-table argument: exactify
each finite vertex group, align both corrections on the words of its shared
edge group, and apply the exact integer restriction equation. The discarded
corners have normalized mass `O(sqrt(E))`; all tables and both edges are
fixed, so the constant is dimension independent.

