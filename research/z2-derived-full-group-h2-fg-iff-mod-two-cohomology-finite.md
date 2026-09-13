---
rg: 2
id: z2-derived-full-group-h2-fg-iff-mod-two-cohomology-finite
kind: claim
title: For free minimal Z^2 Cantor systems, H_2 of the derived full group is finitely generated iff the mod-2 cohomology in degrees one and two is finite
distinct_from:
  derived-full-group-h2-filtered-by-mod-two-groupoid-homology: That is the filtration for any minimal groupoid with comparison; this specializes it to Z^2-actions, where Poincaré duality removes every correction term and gives an exact criterion and the shape Z ⊕ (finite 2-group).
  labbe-shift-derived-full-group-escapes-known-obstructions: That checks recorded obstructions against Labbé's shift; this is a homological criterion for all free minimal Z^2 Cantor systems, which by itself does not decide Labbé's case.
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-2026-09-13.md
---

**ESTABLISHED (unreviewed).**

**Setting.** `Z^2` acts freely and minimally on a Cantor set `X`. Put `D = D([[Z^2 ~ X]])` and
`H^j = H^j(Z^2; C(X, Z/2))`. For subshifts, `H^j` is the mod-2 pattern-equivariant (Čech)
cohomology of the tiling space.

**Theorem 3.**
- `H_2(D; Z)` is finitely generated iff `H^1` and `H^2` are both finite.
- In that case `H_2(D; Z) ≅ Z ⊕ T`, where `T` is a finite abelian 2-group of exponent at most 4
  and `|H^1| · |H^2| / 2 <= |T| <= |H^1| · |H^2|`.
- **Class obstruction.** If `H^1` or `H^2` is infinite, `D` is not finitely presented. When `X`
  is a subshift, `D` is finitely generated
  (`minimal-z2-subshift-derived-full-groups-are-fg-simple`), so the obstruction is sharp in
  degree 2.
- **Products.** For `X = X_1 × X_2`, a product of Cantor minimal `Z`-systems with the product
  action, `H^1 ≅ K^0(X_1) ⊗ Z/2 ⊕ K^0(X_2) ⊗ Z/2` and
  `H^2 ≅ (K^0(X_1) ⊗ Z/2) ⊗ (K^0(X_2) ⊗ Z/2)` (Künneth over `F_2`).
  - So the obstruction fires iff some `K^0(X_i) ⊗ Z/2` is infinite.
  - We did not check whether a minimal `Z`-subshift has infinite `K^0 ⊗ Z/2`.

**Not decided here.** The instances are recorded elsewhere:
- Labbé's shift, whose `H^1` and `H^2` are finite, is treated in part 2 of the artifact.
- The Penrose group, which acts through `Z^2 ⊕ Z/5`, is
  `penrose-derived-full-group-homology-is-finitely-generated`.

Proof: `z2-derived-full-group-h2-criterion-proof`.
