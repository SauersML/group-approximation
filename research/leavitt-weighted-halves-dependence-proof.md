---
rg: 2
id: leavitt-weighted-halves-dependence-proof
kind: route
title: Cut the tree by the weighted prefix code of first passage above weight N, read weighted-nonnegative monomials as matrices over the free algebra on that code, and reuse the minimal-rank and free-field steps
target: leavitt-weighted-halves-have-dependent-commuting-pairs
requires: [leavitt-nonnegative-part-is-matrix-union-over-free-algebra, matrices-over-free-fields-have-no-trdeg-two-subfields]
artifacts:
  - experiments/leavitt-mixed-centralizers-2026-09-17/check_weighted_blocks.py
---

Notation is as in the target. `s_w = s_(w_1) ⋯ s_(w_l)` and `t_w = (s_w)^* = t_(w_l) ⋯ t_(w_1)`. So
`t_v s_w = s_(w')` if `w = v w'`, `t_v s_w = t_(v')` if `v = w v'`, and `t_v s_w = 0` otherwise.
`P = k<x_0, x_1>` and `D = k(<x_0, x_1>)`.

## Step 0. The bigrading

The relations `t_i s_j = δ_ij` and `s_0 t_0 + s_1 t_1 = 1` are homogeneous for `bideg s_0 = (1,0)`,
`bideg s_1 = (0,1)`, `bideg t_i = -bideg s_i`. So `L = ⊕_((m,n) ∈ Z^2) L_(m,n)`, and `L_(m,n)` is spanned by the
`s_w t_v` of that bidegree. For integers `p, q` the map `(m,n) ↦ pm + qn` turns this into a `Z`-grading, and
`L^(p,q)_(>=0)` is spanned by the `s_w t_v` with `φ(w) >= φ(v)`, where `φ(w) = p·#_0 w + q·#_1 w`.

## Step 1. The weighted prefix code (Statement 1)

Fix integers `p, q >= 1` and `N >= 1`. Let `C = C_N` be the set of words `c` with `φ(c) >= N` whose proper
prefixes all have `φ < N`.

- **(a) Finite.** Every letter has weight at least 1, so every word of length `N` has `φ >= N`. Hence
  `C` consists of words of length at most `N`.
- **(b) Complete prefix code.** No element of `C` is a proper prefix of another, by minimality. Every infinite
  word has exactly one prefix in `C`, namely its shortest prefix of weight at least `N`.
- **(c) Matrix units.** For `c, d ∈ C`, `t_c s_d = δ_(c,d)` by (b) and the rule for `t_v s_w`. Also
  `Σ_(c ∈ C) s_c t_c = 1`. This holds by induction on `Σ_c |c|`. A complete finite prefix code other than `{∅}`
  contains two words `z0, z1` of maximal length with a common parent `z`. Replacing them by `z` gives a complete
  prefix code, and `s_(z0) t_(z0) + s_(z1) t_(z1) = s_z (s_0 t_0 + s_1 t_1) t_z = s_z t_z`.
- **(d) The block map.** Define `Ψ : M_C(P) → L` by `Ψ((P_(c,d))) = Σ_(c,d ∈ C) s_c P_(c,d)(s_0, s_1) t_d`.
  - By (c), `Ψ(X) Ψ(Y) = Σ s_c X_(c,d) (t_d s_(d')) Y_(d',e) t_e = Ψ(XY)`, and `Ψ(1) = Σ_c s_c t_c = 1`.
  - `P → L`, `x_i ↦ s_i`, is injective. This is Statement 1 of
    `leavitt-nonnegative-part-is-matrix-union-over-free-algebra` with `N = 0`.
  - Since `t_c Ψ(X) s_d = X_(c,d)(s)`, the map `Ψ` is injective.
  - So `B_N = Ψ(M_C(P))` is a unital subalgebra isomorphic to `M_(|C|)(P)`.
- **(e) Nonnegative monomials lie in `B_N`.** Let `φ(w) >= φ(v)` and `φ(v) < N`.
  - The words `u` with `vu ∈ C` form a complete finite prefix code, by (b), since the prefix of `vz` in `C` is
    longer than `v`.
  - By (c) applied to that code, `t_v = Σ_u s_u t_u t_v = Σ_u s_u t_(vu)`. So `s_w t_v = Σ_u s_(wu) t_(vu)`.
  - For each `u`, `φ(wu) >= φ(vu) >= N`, so `wu = c w''` for a unique `c ∈ C`. Hence
    `s_w t_v = Σ_u s_c s_(w'') t_(vu) ∈ B_N`.
- **(f) Conclusion.** A finite subset of `L^(p,q)_(>=0)` is a combination of finitely many monomials
  `s_w t_v` with `φ(w) >= φ(v)`. Choose `N > max φ(v)`. Then (e) puts the subset in `B_N ≅ M_(|C_N|)(P)`. ∎

`check_weighted_blocks.py` verifies (b), (c) and (e) in normal form over `F_2`. It covers weights `(1,1)`,
`(1,2)`, `(2,1)`, `(2,3)`, `(3,1)` and `(1,4)`, every `N <= 6`, and all monomials with `|w|, |v| <= 4`.

## Step 2. Cone test (Statement 3)

Let `S ⊂ Z^2` be finite, `K = cone(S)`, and `K^* = {ℓ : ℓ·x >= 0 on K}`. Both are rational polyhedral cones.

- **If `ℓ = (α, β)` with `α, β > 0` is nonnegative on `S`.** Then `ℓ < 0` on `Q_- ∖ 0`, so `K ∩ Q_- = {0}`.
- **If `K ∩ Q_- = {0}`.**
  - For polyhedral cones, `(K ∩ Q_-)^* = K^* + Q_-^*`, with no closure needed. Also `Q_-^* = Q_-`.
  - So `K^* + Q_- = R^2`. Write `(1,1) = ℓ + n` with `ℓ ∈ K^*` and `n ∈ Q_-`.
  - Then both coordinates of `ℓ` are at least 1.
- **Rational choice.** `Λ = K^* ∩ (0,∞)^2` is nonempty and relatively open in `K^*`. Rational points are dense
  in the rational polyhedral cone `K^*`, so `Λ` contains a rational point. Scaling it gives integers
  `p, q >= 1`.
- **Membership.** An element whose bidegree support lies in `S` has all components in degrees
  `pm + qn >= 0`. So it lies in `L^(p,q)_(>=0)`. ∎

## Step 3. Dependence (Statement 2)

Let `a, b` commute, and let `K = cone(S(a) ∪ S(b))`.

- **Reduce to one quadrant.** Suppose `K ∩ Q_+ = {0}`. Apply the involution `*` (`s_i ↔ t_i`). It is a
  `k`-linear anti-automorphism, and it negates bidegrees.
  - Since `a` and `b` commute, `f(a,b)^* = f(a^*, b^*)` for every polynomial `f`.
  - So `a^*, b^*` commute and are dependent iff `a, b` are.
  - Now `cone(S(a^*) ∪ S(b^*)) ∩ Q_- = {0}`.
- **The main case.** Assume `K ∩ Q_- = {0}`.
  - By Step 2, `a, b ∈ L^(p,q)_(>=0)` for some integers `p, q >= 1`.
  - By Step 1, `a, b ∈ B ≅ M_n(P) ⊆ M_n(D)`.
- **Contradiction if independent.** Suppose `a, b` are algebraically independent.
  - Then `C = k[a, b] ≅ k[x, y]` is a nonzero commutative subalgebra of `M_n(D)` without zero divisors.
  - By Statement 3 of `leavitt-nonnegative-part-is-matrix-union-over-free-algebra` (quoted there: "Let
    `C ⊆ M_n(D)` be a nonzero commutative `k`-subalgebra without zero divisors ... Then `M_r(D)` has a subfield
    `F`, containing `k · 1`, with `F ≅ Frac(C)`"), some `M_r(D)` has a subfield `F ≅ k(x, y)` containing `k · 1`.
  - `trdeg_k F = 2`. This contradicts `matrices-over-free-fields-have-no-trdeg-two-subfields`. ∎

## Step 4. The example

`a = s_0 + s_0 t_1 t_1` has components `s_0` and `s_0 t_(11)`. Their bidegrees are `(1,0)` and `(1,-2)`, and
their standard degrees are `1` and `-1`. With `(p,q) = (3,1)` the weighted degrees are `3` and `1`. The script
prints this.
