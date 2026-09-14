---
rg: 2
id: lot-torsion-free-via-concatenable-tietze-presentations
kind: route
title: Reduce the LOT, pass to a minima-concatenable Tietze presentation, and read torsion-freeness off local indicability
target: lot-groups-are-torsion-free
requires:
  - lot-reductions-preserve-homotopy-type
  - reduced-lots-have-concatenable-tietze-presentations
  - barreto-minian-concatenable-minima-give-local-indicability
artifacts:
  - research/artifacts/hl-lot-torsion-2026-09-14.md
---

1. **Reduce.** By `lot-reductions-preserve-homotopy-type`, every LOT `Γ` has a reduced LOT `Γ_red` with
   `K(Γ) ≃ K(Γ_red)`, so `G(Γ) ≅ G(Γ_red)`.
2. **Local indicability.** By `reduced-lots-have-concatenable-tietze-presentations`, `G(Γ_red)` has a
   presentation of deficiency `1` with `H_1 = Z`, whose relators are cyclically reduced with total
   exponent `0` and whose multisets of minima of all relators but one are concatenable. By
   `barreto-minian-concatenable-minima-give-local-indicability`, `G(Γ)` is locally indicable.
3. **Torsion-freeness.** A locally indicable group is torsion-free: a nontrivial finite cyclic subgroup
   has no homomorphism onto `Z`.

The route stays blocked on step 2, which is open.
