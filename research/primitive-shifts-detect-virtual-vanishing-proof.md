---
rg: 2
id: primitive-shifts-detect-virtual-vanishing-proof
kind: route
title: Direct proof of the primitive-shift dictionary from Z-contractibility of free resolutions
target: primitive-shifts-detect-virtual-vanishing
requires: []
artifacts:
  - research/artifacts/primitive-shift-goodness-dictionary-2026-09-18.md
---

## Why sufficient

This is a complete elementary proof. Full details are in §§1–3 of the artifact.

1. **SFT.** In the coordinates `v(g)_j = g^{-1}ψ(g e_j)`, the `G`-action becomes the left
   shift. The condition `ψ∘∂_q = z` becomes the local rules
   `Σ_{j,s} a_{ijs} s·v(gs)_j = z(e'_i)`, whose right-hand side does not depend on `g`.
   So `Σ(z)` is an SFT with window `S`, the support of the matrix of `∂_q`.
2. **Nonempty.** `F_* -> Z` is an exact complex of free abelian groups, so it is
   contractible over `Z`. Hence `Hom_Z(F_*, A)` is exact, and the cocycle `z` is
   `ψ∘∂_q` for some `ψ`.
3. **Torsor and measure.** `Σ(z)` is a torsor under the group shift `Σ_0 = {ψ∘∂_q = 0}`,
   on which `G` acts by automorphisms. Haar measure is preserved by continuous
   automorphisms, so its transport to `Σ(z)` is `G`-invariant, independent of the base
   point, and of full support.
4. **Fixed points.** An `H`-fixed `ψ` is an element of `Hom_H(F_{q-1}, A)` with
   `ψ∘∂_q = z`. Since `F_*` is a free `ZH`-resolution, such a `ψ` exists exactly when
   `res^G_H x = 0`.
5. **Terminal effacer.** Elements `c ∈ Hom_G(F_{q-1}, C(X, A))` with `c∘∂_q = z` (as
   constants) correspond bijectively to continuous `G`-maps `Φ: X -> Σ(z)`, via
   `Φ(y)(σ) = c(σ)(y)`. Equivariance follows from `(g·f)(y) = g·f(g^{-1}y)` and
   `G`-linearity of `c`.
6. **Consequences.**
   - A finite orbit is an `H`-fixed point with `[G:H] < ∞`.
   - The statement about `FP_∞` groups applies this to each class separately.
   - **Odometer.** The image of an equicontinuous system in the expansive shift is both
     equicontinuous and expansive, hence finite.
7. **Periodic density.** The set `{λ(1) = 1}` is clopen and nonempty. A periodic point
   inside it is an `H`-fixed point of `Σ(z)` with `[G:H] < ∞`.

No external result is used. The identification of "every class effaceable" with
goodness appears only as a reading in the claim. It is not part of what this route
proves.
