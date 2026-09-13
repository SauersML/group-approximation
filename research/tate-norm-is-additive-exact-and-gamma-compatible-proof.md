---
rg: 2
id: tate-norm-is-additive-exact-and-gamma-compatible-proof
kind: route
title: Free orbits of tensor words die against the Tate object; the equivariantly split Izumi filtration gives triangles
target: tate-norm-is-additive-exact-and-gamma-compatible
requires: [nishikawa-petrosyan-equivariant-power-functor, zp-restriction-trivial-splits-cellular-plus-phantom]
artifacts: [research/artifacts/uct-tate-diagonal-wreath-cone-2026-09-13-part3.md]
---

The full derivation is `research/artifacts/uct-tate-diagonal-wreath-cone-2026-09-13-part3.md` §9.

- **Item 1.** Nishikawa–Petrosyan Thm. 5.10, then `q^*1_T ⊗ −`.
- **Item 2.**
  - `(A ⊕ B)^(⊗p)` is the direct sum of tensor words.
  - Non-constant words form free `G`-orbits (`p` prime), so each orbit sum is `Ind_(Γ^p)^W`.
  - `Res^W_(Γ^p) q^*1_T` inflates `Res^G_1 1_T ≃ 0`, so those orbit sums die.
  - Constant words are preserved by the powers of the canonical inclusions and projections.
  - A functor preserving biproducts is additive.
- **Item 3.**
  - Nishikawa–Petrosyan Prop. 5.18 gives equivariantly c.c.p.-split steps in the Izumi filtration
    of `M_φ^(⊗p)`, hence triangles.
  - The middle layers `⊕_(|S| = j) C_φ^(⊗S) ⊗ B^(⊗Ω∖S)` with `0 < j < p` are induced and die.
  - The bottom layer is `C_φ^(⊗p)`, and the top quotient is `B^(⊗p)`.
  - `M_φ^(⊗p) ≅ A^(⊗p)` by functoriality.
- **Item 4.**
  - `T(γA)` is cellular by Nishikawa–Petrosyan Lemma 5.19.
  - `T((1 − γ)A)` is weakly contractible: over conjugates of `<σ>` it is `N^(⊗p)` with `N ≃_KK 0`,
    which is equivariantly contractible by Lemma 5.15 and functoriality.
  - Additivity and the uniqueness in Meyer–Nest Thm. 8.3 (arXiv:math/0312292v3) finish the proof.
- **Item 5.** `(Ind_K^Γ B)^(⊗p) = Ind_(K≀G)^W B^(⊗p)`, and induction commutes with `⊗ q^*1_T`.

The Tate object and its vanishing restriction are recorded in
`zp-restriction-trivial-splits-cellular-plus-phantom` and in part 2 §8 of the norm-functor artifact.
