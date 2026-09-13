---
rg: 2
id: quantum-rigidity-passes-to-sub-sfts-proof
kind: route
title: A local family of the sub-SFT is a local family of the ambient SFT at the smaller scale
target: quantum-rigidity-passes-to-sub-sfts
requires: [sft-crossed-product-fp-iff-quantum-rigid]
---

Let `E` be a `D''`-family for `Ω`, with `D'' = max(D, r')`.

1. **(Q1).** It holds unchanged.
2. **(Q2) at scale `D`.** Pairs at distance `<= 2D <= 2D''` commute.
3. **(Q3) at scale `D` for `X`.**
   - Fix `z` and a `B_D`-pattern `π` not occurring in `X`. The operators `E(w)` for `w ∈ z + B_(D'')` commute
     pairwise, because the ball has diameter `2D''`.
   - Inserting `1 = prod_(w ∈ B_(D'') \ B_D) sum_a E_a(z + w)` writes `prod_(h ∈ B_D) E_(π(h))(z + h)` as the sum,
     over extensions `π'` of `π` to `B_(D'')`, of `prod_(h ∈ B_(D'')) E_(π'(h))(z + h)`.
   - An extension `π'` occurring in `Ω` would restrict to a pattern `π` occurring in `X`, since `Ω ⊆ X`. So no
     `π'` occurs in `Ω`, every term vanishes by (Q3) for `Ω`, and the product over `π` vanishes.
4. **Rigidity.** So `E` is a `D`-family for `X`, and it commutes because `X` is `D`-quantum rigid. Hence `Ω` is
   `D''`-quantum rigid.
5. **Finite presentation.** The cited claim, with `D'' >= r'`, gives that `LC(Ω, k) ⋊ Z^2` is finitely
   presented.
