---
rg: 2
id: simple-ring-with-matrix-units-el-lef-iff-matricial
kind: claim
title: For a simple ring containing nonzero 2x2 matrix units, one LEF elementary group of rank at least two is equivalent to a matrix ultraproduct embedding over finite fields
distinct_from:
  lef-el-groups-force-exactly-matricial-simple-ring: that is the equivalence from one LEF elementary group of rank at least four, for every simple ring; this reaches ranks two and three, for simple rings containing nonzero 2x2 matrix units.
---

**ESTABLISHED (unreviewed; route `simple-ring-with-matrix-units-el-lef-iff-matricial-proof`).**

Let `R` be a countable simple unital ring containing `ε_ij`, `i, j ∈ {1,2}`, with `ε_ij ε_kl = δ_jk ε_il` and
`ε_11 != 0`. The following are equivalent:

1. `EL_N(R)` is LEF for one `N >= 2`;
2. `R` is a LEF ring;
3. `R` embeds unitally in an algebraic ultraproduct `prod_omega M_(d_n)(F_(q_n))` over finite fields;
4. `GL_N(R)` and `EL_N(R)` are LEF for every `N >= 1`.

So at the note's own ranks 2 and 3, rung (L) of `kazhdan-elementary-approximation-type-mirrors-ring-type` is an
equivalence for these rings: LEF `EL_N` ⟺ LEF ring ⟺ exactly matricial.

**Scope.**
- Every simple Steinberg algebra `A_k(𝒢)` of a minimal effective Hausdorff ample groupoid with infinite unit space
  (`steinberg-algebra-simple-iff-minimal-effective`). There is an arrow `g` with `r(g) != s(g)`, and a compact open
  bisection `σ ∋ g` with `r(σ) ∩ s(σ) = ∅` gives `ε_12 = 1_σ`, `ε_21 = 1_(σ^{-1})`, `ε_11 = 1_(r(σ))`,
  `ε_22 = 1_(s(σ))`.
- In particular `LC(X,k) ⋊ Γ` for every minimal topologically free action of a countable group on an infinite
  Cantor set. Take `γ != e` and a clopen `V != ∅` with `γV ∩ V = ∅`, and `ε_12 = u_γ e_V`, `ε_21 = e_V u_γ^{-1}`.
- Purely infinite simple rings such as `L_k(1,2)`, where all four conditions fail.
- Not covered: simple rings with no nonzero 2x2 matrix units, e.g. division rings and simple domains
  (`simple-ring-el3-lef-forces-lef-ring`, open).

**Consequence.** With `lef-simple-rings-are-not-finitely-presented`: a finitely presented infinite simple ring with
nonzero 2x2 matrix units has no LEF elementary group of any rank `N >= 2`. For example, if a free minimal
`Z^2`-SFT crossed product `LC(X,F_q) ⋊ Z^2` is finitely presented, then its `EL_2` and `EL_3` are not LEF.

**Model test.** `M_2(F_2 × F_2)` satisfies (1), (2) and (4). Its unital maps onto one matrix factor are not
injective, so simplicity is used only in (2) ⇒ (3).

**Review (sk-verify-8, 2026-09-13, `research/artifacts/sk-review-8-2026-09-13-part3.md`):** PASS (§3). (1)⇒(2)⇒(3)⇒(4)⇒(1), and the Steinberg bisection argument, re-derived. N4: the model test fails as stated. `M_2(F_2 × F_2)` satisfies (3) through the diagonal embedding into `M_4(F_2)`, and simplicity is also used in (1)⇒(2). A test that simplicity is needed in (2)⇒(3) is `M_2(Z/4)`: it has full matrix units and is finite, but `4 = 0` has no unital image in matrices over fields. N5: the Steinberg bullet needs a compact, second countable unit space, so that `R` is unital and countable.
