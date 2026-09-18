---
rg: 2
id: amenable-principal-fp-group-algebras-are-domains-proof
kind: route
title: Dimension-flatness and integral Baum--Connes traces kill annihilators of finite type over amenable group algebras
target: amenable-principal-fp-group-algebras-are-domains
requires: []
---

Throughout, `G` is torsion-free and amenable, `k ⊆ C` is a subfield (the claim uses `k = Q`), `NG`
is the group von Neumann algebra with its faithful normal trace `tr`, and `dim = dim_NG` is Lück's
extended dimension on all `NG`-modules. Modules are left modules; `NG` is a right `k[G]`-module
through `k[G] ⊆ C[G] ⊆ NG`.

## Imports

- **(I1) Additivity.** `dim` is additive on short exact sequences of `NG`-modules, monotone on
  submodules and quotients, and `dim NG^m e = tr(e)` for an idempotent `e ∈ M_m(NG)`
  (W. Lück, *L²-invariants*, Springer 2002, Theorem 6.7 and Section 6.1; the trace of an idempotent equals the trace of the projection
  with the same range).
- **(I2) Dimension-flatness.** If `G` is amenable, then `dim Tor_p^{C[G]}(NG, M) = 0` for every
  `p >= 1` and every `C[G]`-module `M` (Lück, *op. cit.*, Theorem 6.37). Since `C[G] = C ⊗_k k[G]`
  is free over `k[G]`, `Tor_p^{k[G]}(NG, M) ≅ Tor_p^{C[G]}(NG, C[G] ⊗_{k[G]} M)`, so the same
  vanishing holds over `k[G]`.
- **(I3) Integral traces.** If `H` is a countable torsion-free amenable group, then `tr(e) ∈ Z`
  for every idempotent matrix `e` over `C*_r H`. Source: Higson--Kasparov (Invent. Math. 144
  (2001)) prove the Baum--Connes conjecture for a-T-menable, in particular amenable, countable
  groups; for torsion-free groups surjectivity of the assembly map gives
  `tr(K_0(C*_r H)) ⊆ Z` (Lück, Invent. Math. 149 (2002), "The relation between the Baum--Connes
  conjecture and the trace conjecture"; also Mislin--Valette, *Proper group actions and the
  Baum--Connes conjecture*, Birkhäuser 2003, Part II). The trace of an idempotent depends only on its
  `K_0`-class.
- **(I4) Positivity.** If `0 != b ∈ NG`, then `dim NG b > 0`: `NG b ≅ NG/ann_l(b)` and
  `ann_l(b) = NG(1-q)` for the (nonzero) range projection `q` of `b`, so `dim NG b = tr(q) > 0`
  by faithfulness of `tr` (Lück, *op. cit.*, Theorem 6.7 and §6.1).
- **(I5) Projective dimension.** For every `k[G]`-module `M`,
  `Ext^i_{k[G]}(M, N) ≅ H^i(G; Hom_k(M, N))` with the diagonal action (K. Brown, *Cohomology of
  groups*, III.2.2, valid because `M` is `k`-free). Hence `pd_{k[G]} M <= cd_k G`.

## Step 0: traces over `k[G]` are integral

Let `e ∈ M_m(k[G])` be idempotent. Its entries have finite support, so `e ∈ M_m(k[H])` for a
finitely generated, hence countable, subgroup `H <= G`, which is torsion-free and amenable. The
trace `tr_G` restricts to `tr_H` on `C[H]`, and `k[H] ⊆ C*_r H`. By (I3), `tr(e) ∈ Z`.

Consequently, if `P` is a finitely generated projective `k[G]`-module, `P ≅ k[G]^m e`, then
`NG ⊗_{k[G]} P ≅ NG^m e` and `dim(NG ⊗_{k[G]} P) = tr(e) ∈ Z` by (I1).

## Step 1: Euler characteristic of a module of type FP

Let `L` be a `k[G]`-module with a resolution `0 → P_r → ... → P_0 → L → 0` by finitely generated
projectives. Tensor with `NG`. The resulting complex `NG ⊗ P_•` has homology `NG ⊗ L` in degree 0
and `Tor_p^{k[G]}(NG, L)` in degree `p >= 1`, which has dimension 0 by (I2). All terms have finite
dimension. Additivity (I1), applied to the short exact sequences of cycles, boundaries and
homology, gives

`dim(NG ⊗_{k[G]} L) = Σ_p (-1)^p dim(NG ⊗ P_p) ∈ Z`

by Step 0.

## Step 2: an annihilator of type FP is zero

Fix `0 != a ∈ k[G]` and put `L = ann_l(a) = {x ∈ k[G] : xa = 0}`. There are exact sequences

`0 → L → k[G] → k[G]a → 0` (the middle map is `x ↦ xa`) and `0 → k[G]a → k[G] → k[G]/k[G]a → 0`.

**Dimension of `L`.** Tensor the second sequence with `NG`. The map
`NG ⊗ k[G]a → NG ⊗ k[G] = NG` has image `NG a` and kernel a quotient of
`Tor_1^{k[G]}(NG, k[G]/k[G]a)`, of dimension 0 by (I2). So `dim(NG ⊗ k[G]a) = dim NG a > 0` by
(I4). Tensor the first sequence: `NG ⊗ L → NG → NG ⊗ k[G]a → 0` is exact and the kernel of the
first map is a quotient of `Tor_1^{k[G]}(NG, k[G]a)`, of dimension 0. By (I1),

`dim(NG ⊗ L) = 1 - dim NG a ∈ [0, 1)`.

**Integrality.** Suppose `L` is of type `FP` over `k[G]`. By Step 1, `dim(NG ⊗ L) ∈ Z`, so it is
0.

**Vanishing.** The image of `NG ⊗ L → NG` is the left ideal `NG·L`, a quotient of `NG ⊗ L`, so
`dim NG·L = 0` by (I1). If some `0 != b ∈ L` existed, then `NG b ⊆ NG·L` and (I4) would give
`dim NG·L > 0`. Hence `L = 0`.

## Step 3: principal ideals versus annihilators

Two standard facts about a ring `R` (Brown, *Cohomology of groups*, VIII.4.3 and VIII.6.1, whose
proofs are module-theoretic and apply to any ring; also R. Bieri, *Homological dimension of
discrete groups*, Proposition 1.4):

- **(F1)** If `0 → K → P → M → 0` is exact with `P` finitely generated projective and `M` of type
  `FP_∞`, then `K` is of type `FP_∞`.
- **(F2)** A module of type `FP_∞` and finite projective dimension `d` is of type `FP`: in a
  resolution `... → P_1 → P_0 → M` by finitely generated projectives, the kernel of
  `P_{d-1} → P_{d-2}` is projective (dimension shifting) and finitely generated (image of `P_d`).

Apply them to `0 → L → k[G] → k[G]a → 0`. If `k[G]a` is of type `FP` (so `FP_∞` with
`pd <= r` for some `r`), then `L` is of type `FP_∞` by (F1), and `pd L <= max(r-1, 0)` by dimension
shifting, so `L` is of type `FP` by (F2).

## Step 4: conclusion

**(1), "if".** Assume every `k[G]a` is of type `FP`. By Step 3 each `ann_l(a)` is of type `FP`, and
by Step 2 it is 0 for `a != 0`. If `ab = 0` with `a, b != 0`, then `a ∈ ann_l(b) = 0`, a
contradiction. So `k[G]` is a domain.

**(1), "only if".** If `k[G]` is a domain and `a != 0`, then `x ↦ xa` is injective, so
`k[G]a ≅ k[G]` is free of rank 1, which is of type `FP`; `k[G]0 = 0` is of type `FP`.

**(2).** If `cd_k G = n < ∞`, every `k[G]`-module has `pd <= n` by (I5), so a module of type
`FP_∞` is of type `FP` by (F2), and (1) applies.

**(3).** If `k[G]` is left coherent, every finitely presented left module is of type `FP_∞`
(finitely generated submodules of finitely presented modules are finitely presented, so syzygies
stay finitely presented). `k[G]a` is a finitely generated left ideal of a coherent ring, hence
finitely presented, hence of type `FP_∞`. Apply (2) and (1). Finally `cd_k G <= cd_Z G` and
`Z[G] ⊆ Q[G]`, so a domain `Q[G]` gives a domain `Z[G]`. ∎

## Remarks

- Amenability enters only through (I2). For non-amenable `G` the tensor functor `NG ⊗ -` is not
  dimension-exact (for `F_2` one has `dim Tor_1(NG, Q) = b_1^(2)(F_2) = 1`), and Step 2 breaks at
  the additivity computation of `dim(NG ⊗ L)`.
- Calibration. For `G = Z^d` the ring `Q[G]` is Noetherian of global dimension `d`, and the proof
  reduces to the classical argument that ranks of finitely generated modules with finite free
  resolutions are integers. For the finite group `Z/2` (not torsion-free) Step 0 fails:
  `e = (1+g)/2` has trace `1/2`, and indeed `(1+g)(1-g) = 0`. So torsion-freeness enters exactly
  at the integrality import (I3).
