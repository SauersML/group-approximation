---
rg: 2
id: primitive-shifts-detect-virtual-vanishing
kind: claim
title: The primitive shift of a finite-coefficient class is its terminal effacer, and its fixed-point subgroups are exactly the subgroups killing the class
artifacts:
  - research/artifacts/primitive-shift-goodness-dictionary-2026-09-18.md
---

**Setup.** Let `G` be of type `FP_q` with `q >= 1`, and let `F_*` be a free resolution
with `F_{q-1} = ZG^m` and `F_q` of finite rank. Let `A` be a finite `G`-module, and let
`z ∈ Hom_G(F_q, A)` be a cocycle for `x ∈ H^q(G; A)`. Put
`Σ(z) := {ψ ∈ Hom_Z(F_{q-1}, A) : ψ∘∂_q = z}` with the action `(g·ψ)(σ) = g·ψ(g^{-1}σ)`.

1. **Structure.** In the coordinates `v(g)_j = g^{-1}ψ(g e_j)`, the space `Σ(z)` is a
   nonempty shift of finite type in `(A^m)^G`. It is an affine torsor under a group shift,
   and it carries a shift-invariant Haar probability measure of full support.
2. **Fixed points.** For every subgroup `H <= G`, we have `res^G_H x = 0` exactly when
   `Σ(z)^H ≠ ∅`.
3. **Terminal effacer.** For every compact Hausdorff `G`-space `X`, the image of `x` in
   `H^q(G; C(X, A))` vanishes exactly when there is a continuous `G`-map `X -> Σ(z)`.
4. **Consequences.**
   - `x` is effaceable exactly when `Σ(z)` has a finite orbit.
   - For a group of type `FP_∞`, every positive-degree finite-coefficient class is
     effaceable exactly when all its positive-degree primitive shifts have finite orbits.
     By Serre's criterion, which is recorded separately as
     `effaceable-cohomology-makes-inflation-an-isomorphism` and not used here, this is
     goodness.
   - If `x` dies over a profinite odometer, then it is effaceable.
5. **Periodic density.** Let `Σ^+(z) ⊂ (A^m × Z/e)^G` be the group SFT that adjoins a
   constant scalar `λ` and imposes `ψ∘∂_q = λz`. If its periodic points are dense, then `x`
   is effaceable.

**Reading.**
- The theorem is the symbolic dictionary for Serre goodness.
- Every other property that a symbolic proof might give an effacer comes for free from
  `Σ(z)` or from its products with free subshifts: finite type, invariant measure,
  minimality, freeness, expansiveness. Existence of a periodic point in `Σ(z)` is the
  cohomological statement itself.
- On `Γ(3) <= SL_3(Z)`, the persistent degree-two classes of
  `sl3z-level-three-fails-degree-two-goodness` give primitive shifts with an invariant
  measure and no finite orbit.

Derivation: `primitive-shifts-detect-virtual-vanishing-proof`.
