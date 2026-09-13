---
rg: 2
id: radu-horizontal-tree-group-is-linear
kind: claim
title: Radu's BMW lattice acts on its horizontal tree through PGL_2 of a number field on the 2-adic Bruhat-Tits tree, so it is free-by-linear and acts faithfully on its vertical tree
distinct_from:
  radu-horizontal-projection-kills-delta-squared: that proves (xz)^2 acts trivially on the horizontal tree and computes level orders; this identifies the whole horizontal action with a linear representation, so the kernel of that action is the kernel of the representation
  radu-bmw-lattice-embeds-in-titz-witzel-kernel: that imports the lattice, its presentation and Titz Mite-Witzel's linear representation of the derived subgroup; this extends the representation to the lattice in PGL_2 form and proves that 2-adically it is the horizontal tree action
  radu-lattice-induced-actions-are-never-mixing: that uses the infinite horizontal kernel to exclude induced mixing actions; this computes that kernel and the horizontal closure exactly
---

**ESTABLISHED (unreviewed).** Let `Γ_R = <a,b,c,x,y,z | involutions, axax, ayay, azbz, bxbx, bycy, cxcz>`
be Radu's BMW lattice acting on `T_h × T_v` (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`),
with `V = <x,y,z>` and `Λ_v = ker(Γ_R → Aut(T_h))`. Let `m ∈ Z_2` be the root with
`v_2(m) = 1`, `s ∈ Z_2`, and `K = Q(m, s) ⊂ Q_2` (a number field of degree at most 8), where

```text
2m^4 − m^3 + 2m^2 − m + 2 = 0,        s^2 = −4(m^2 + m + 1),
```

and define, in `PGL_2(K)`,

```text
ρ(x) = [[1,0],[0,−1]],  ρ(z) = [[0,1],[1,0]],  ρ(y) = [[s,−2m],[2,−s]],  ρ(a) = [[0,m],[1,0]],
ρ(b) = ρ(zaz),          ρ(c) = ρ(yby).
```

1. **Representation.** `ρ` is a homomorphism `Γ_R → PGL_2(K)`, and `ρ((xz)^2) = ρ((xyz)^3) = 1`.
2. **It is the horizontal tree action.** `Γ_R ↷ T_h` is equivariantly isomorphic to `ρ`
   followed by the action of `PGL_2(Q_2)` on its Bruhat–Tits tree. Hence `Λ_v = ker ρ`.
3. **Free-by-linear.** `Q = Γ_R/Λ_v ≅ ρ(Γ_R)` is a finitely generated linear group, hence
   residually finite. So the finite residual of `Γ_R`, which contains the mark `(xz)^4`, lies in
   `Λ_v`. `Λ_v` is an infinitely generated free group, and `T_v/Λ_v` is the Cayley graph of
   `ρ(V)`, a quotient of the Coxeter group `<x,y,z | x^2,y^2,z^2,(xz)^2,(xyz)^3> ≅ PGL_2(Z)`.
   `Γ_R` is the group of lifts to `T_h × T_v` of the action of `Q` on `T_h × T_v/Λ_v`.
4. **Horizontal closure.** The closure `H_h` of the horizontal projection is an open subgroup of
   `PGL_2(Q_2)`. Its vertex stabilizer contains the principal congruence subgroup of level 8 and
   has index 2 in `PGL_2(Z_2)`.
5. **Faithful vertical action.** `QZ(H_h) = 1`, so `ker(Γ_R → Aut(T_v)) = 1`, and `Γ_R` embeds in
   `Aut(T_v)` as a non-discrete subgroup.

**Credit.** Titz Mite–Witzel (arXiv:2509.05054v2, Remark 3.6) constructed a representation
`Φ : D → SL_2(Q(√−15, √17))` of the index-8 derived subgroup, found through congruence quotients,
and used it to show that `δ^(±4)` are the shortest elements of the finite residual. `ρ` is
consistent with it on the one invariant checked: `tr Φ(ba) = −(1+√17)/4`, while
`tr^2/det ρ(ba) = (m + 1/m)^2` with `m + 1/m ∈ {(1 ± √17)/4}`. The explicit PGL_2 form here was derived independently. Items 2–5,
identifying `Φ` with the horizontal tree action, are not in Titz Mite–Witzel (pages 9–11 read)
or in Radu's arXiv:1712.01091 (pages 1–8 read).

**Checks.** The relations were verified by exact arithmetic in `Q[m,s]`. Items 2 and 4 were
checked 2-adically: the orders of `<ρ(x), ρ(y), ρ(z)>` in `PGL_2(Z/2^n)` are
`6, 48, 192, 1536, 12288, 98304` for `n = 1..6`, equal to the level orders of the horizontal
automaton recorded in `radu-horizontal-projection-kills-delta-squared`.

Proof in `radu-horizontal-tree-group-is-linear-proof`.
