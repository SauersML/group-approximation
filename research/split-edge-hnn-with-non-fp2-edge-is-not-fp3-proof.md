---
rg: 2
id: split-edge-hnn-with-non-fp2-edge-is-not-fp3-proof
kind: route
title: "Proof of the split-edge FP_3 obstruction by Bieri-Eckmann on product coefficients"
target: split-edge-hnn-with-non-fp2-edge-is-not-fp3
requires: []
---

Work over `Z`; the argument over `Q` is identical. Modules are left modules,
and `H_*(B; M) = Tor^{ZB}_*(Z, M)`.

**(0) Tools.**

- **(Bieri--Eckmann.)** A module `M` is of type `FP_n` iff
  `Tor_k(M, Π R) → Π Tor_k(M, R)` is an isomorphism for `k < n` and onto for
  `k = n`. For `M = Z` over `ZB` with `B` finitely generated this reads: `B`
  is `FP_2` iff `H_1(B; Π_I ZB) = 0` for all `I`, and `B` is `FP_3` iff
  moreover `H_2(B; Π_I ZB) = 0` for all `I`.
- **(Products of free modules.)** If `B` is of type `FP_2` and `(F_i)` are
  free `ZB`-modules of any ranks, then `H_1(B; Π_i F_i) = Π_i H_1(B; F_i) = 0`.
  Compute with a resolution by finitely generated free modules through
  degree 2; tensoring with such modules commutes with products.
- **(Coinvariants.)** If `B` is finitely generated, then `Z` is a finitely
  presented `ZB`-module, so `Z ⊗_{ZB} (Π_i M_i) = Π_i (Z ⊗_{ZB} M_i)`.

**(1) Choose coefficients.** By hypothesis 1 and Bieri--Eckmann, pick `I`
with `D := H_1(L; Π_I ZL) ≠ 0`, and put `X = Π_I ZK`. For every subgroup
`B ≤ K`, `ZK` is a free `ZB`-module, so the restriction of `X` to `B` is a
product of free `ZB`-modules.

**(2) Mayer--Vietoris.** The HNN sequence with coefficients `X` contains
`H_2(K; X) → H_1(L; X) --φ--> H_1(A; X)`, where
`φ = (f_1)_* − τ (f_2)_*`. Here `τ` is the isomorphism induced by `x ↦ t x`,
which intertwines the two restrictions of `X` to `L`. So `H_2(K; X)` surjects
onto `ker φ`.

**(3) `f_1` is zero in degree 1.** `(f_1)_*` factors through `H_1(P; X)`,
which vanishes by (0) because `P` is `FP_2`. So `ker φ ≅ ker (f_2)_*`.

**(4) Compute `(f_2)_*`.** Let `Γ = f_2(L) ≅ L`, so `A = N ⋊ Γ`. In the
Lyndon--Hochschild--Serre spectral sequence of `1 → N → A → A/N ≅ Γ → 1`,
`E^2_{0,1} = H_0(Γ; H_1(N; X)) = 0` by (0), because `N` is `FP_2`. Hence
the edge map `H_1(A; X) → H_1(Γ; X_N)` is an isomorphism, with
`X_N = H_0(N; X)`. The composite `Γ → A → A/N` is the identity. So
`ker (f_2)_*` is the kernel of the coefficient-induced map
`c_*: H_1(Γ; X) → H_1(Γ; X_N)`.

**(5) The collapse is a split sum map.** Every `a ∈ A` is uniquely `a = γn`
with `γ ∈ Γ` and `n ∈ N`, and left multiplication by `Γ` only moves `γ`. So
`ZA = ⊕_{n ∈ N} ZΓ·n` as a left `ZΓ`-module. The collapse
`ZA → Z[N\A] ≅ ZΓ` is the sum map `(x_n) ↦ Σ_n x_n`.

Write `ZK = ⊕_J ZA` as a left `ZA`-module. By (0) the coinvariants commute
with the product (`N` is finitely generated), so as `ZΓ`-modules
`c: X = Π_I ⊕_J ⊕_{n ∈ N} ZΓ → X_N = Π_I ⊕_J ZΓ` is the sum map in each
coordinate.

It is split onto, by the inclusion of the `n = 1` summands, and its kernel is
`Q' ≅ Π_I ⊕_J ⊕_{n ≠ 1} ZΓ`, through `x ↦ (−Σ_{n≠1} x_n, x)`; the sums are
finite. So `ker c_* = H_1(Γ; Q')`.

**(6) Non-vanishing.** `N ≠ 1` and `J ≠ ∅`. Fix one `j_0 ∈ J` and one
`n_1 ∈ N ∖ {1}`. Then `Π_I ZΓ` is a direct summand of `Q'`, since products
commute with finite direct sums. So `H_1(Γ; Q')` contains
`H_1(Γ; Π_I ZΓ) ≅ D ≠ 0` as a direct summand.

**(7) Conclusion.** `ker φ ≠ 0`, so `H_2(K; Π_I ZK) ≠ 0`. By Bieri--Eckmann
`K` is not of type `FP_3`.

**Calibrations.**

- Hypothesis 1 is needed. If `L` is `FP_2`, then (3)–(6) still identify
  `ker φ`, but `D = 0`. This is why the Fournier-Facio--Zaremsky
  ascending-HNN trick, whose edge groups are finitely presented or `FP_n`,
  is not affected.
- Hypothesis 2's condition `N ≠ 1` is needed. If `N = 1`, then `f_2` is an
  isomorphism `L ≅ A`, `c` is the identity, and no kernel appears.
