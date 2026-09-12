---
rg: 2
id: hyperbolic-kazhdan-cover-of-leavitt-unit-group-proof
kind: route
title: Run the Belegradek--Osin construction on an Sp(2,1) lattice over the finitely presented Kazhdan unit group
target: hyperbolic-kazhdan-cover-of-leavitt-unit-group
requires:
  - belegradek-osin-rips-construction
  - torsion-free-hyperbolic-kazhdan-partner-exists
  - leavitt-unit-group-finitely-presented
  - openai-nine-leaf-leavitt-configuration
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

1. **Source.** Let `H` be a torsion-free cocompact lattice in `Sp(2,1)`
   (`torsion-free-hyperbolic-kazhdan-partner-exists`). It is non-elementary,
   word-hyperbolic and Kazhdan.
2. **Quotient.**
   - `R^x` is finitely presented (`leavitt-unit-group-finitely-presented`,
     Khanh Theorem 6.1).
   - `R^x` is Kazhdan. The nine-leaf configuration gives Kazhdan
     `EL_D(R) ~= EL_9(R)`. The prefix-code isomorphism `M_9(R) ~= R` carries
     `GL_9(R) = EL_9(R)` (`leavitt-gl-equals-el-and-perfect-unit-group`) onto
     `R^x`, so `EL_D(R) = R^x`.
3. **Rips.** `belegradek-osin-rips-construction` gives
   `1 -> N -> G -> R^x -> 1` with `G` hyperbolic and `N` a quotient of `H`.
   - `N` is Kazhdan because it is a quotient of `H`.
   - `G` is Kazhdan as an extension of the Kazhdan group `R^x` by `N`.
4. **`N` is infinite.** If `N` were finite, `G -> R^x` would be a
   quasi-isometry, so `R^x` would be hyperbolic. But `R^x` contains Thompson's
   `V` (the configuration's `J`), and `V` contains `Z^2`, which no hyperbolic
   group contains.
5. **Finite images.** Let `phi : G -> F` with `F` finite. Then `phi(N)` is
   normal in `phi(G)`, and `phi(G)/phi(N)` is a finite quotient of `R^x`.
   `R^x` is simple and infinite (`binary-leavitt-unit-group-is-simple`), so
   this quotient is trivial and `phi(N) = phi(G)`. ∎
