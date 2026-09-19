---
rg: 2
id: leavitt-subfield-bound-from-hochschild-dimension
kind: route
title: The Leavitt algebra is quasi-free, and quasi-free algebras have no transcendence-degree-two subfields in any matrix ring
target: leavitt-algebras-have-no-trdeg-two-subfields
requires: [leavitt-algebra-hochschild-dimension-at-most-one, quasi-free-algebras-have-no-trdeg-two-subfields]
---

1. By `leavitt-algebra-hochschild-dimension-at-most-one`, `pd_(L^e) L <= 1` for every field `k`.
2. Item 3 of `quasi-free-algebras-have-no-trdeg-two-subfields`, with `A = L`, gives the subfield bound in
   `M_r(L)`.
3. For the equivalent form, let `a, b` commute with every nonzero `p(a, b)` invertible.
   - Then `p(a, b) ≠ 0` for every `p ≠ 0`, so `a` and `b` are algebraically independent.
   - The inverses commute with each other and with `a, b`.
   - So `{p(a, b) q(a, b)^(-1)}` is a subfield isomorphic to `k(x, y)` and containing `1`, which contradicts step 2.

∎

**Self-contained check of step 1.** `L` is the universal localization of `P = k<s_0, s_1>` that inverts the row
`(s_0 s_1) : P^2 -> P`. Its inverse is the column `(t_0; t_1)`, and the Leavitt relations say exactly this.
- A derivation `δ : P -> N` into an `L`-bimodule gives `P -> [[L, N], [0, L]]`. This map inverts the row, by the
  triangular inverse formula.
- So it extends uniquely over `L`, which gives `Der(L, N) ≅ N^2` and `Ω_k(L) ≅ (L^e)^2`.
- This uses only the presentation of `L`, not Ara--Cortiñas flatness.
