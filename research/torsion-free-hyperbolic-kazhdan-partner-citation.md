---
rg: 2
id: torsion-free-hyperbolic-kazhdan-partner-citation
kind: route
title: Take a torsion-free cocompact lattice in Sp(2,1)
target: torsion-free-hyperbolic-kazhdan-partner-exists
requires: []
artifacts:
  - research/artifacts/arithmetic-single-defect-saturation-2026-08-23.md
---

## Direct proof from the literature

Let `G = Sp(2,1)` and let `Gamma <= G` be a cocompact lattice.

- **Property (T).**  `Sp(n,1)` for `n >= 2` has property (T) — the rank-one
  exception to the rank-at-least-two picture, together with `F_4(-20)`.  See
  Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*, CUP 2008, Chapter 3.
  Property (T) passes to lattices, hence to `Gamma`, and thence to every
  finite-index subgroup.
- **Hyperbolicity.**  `G` is a rank-one simple Lie group, so its symmetric
  space is negatively curved; a cocompact lattice acts properly cocompactly by
  isometries on it, so by the Svarc--Milnor lemma `Gamma` is quasi-isometric to
  that space and is therefore word-hyperbolic, and finitely presented.
- **Torsion-freeness.**  Selberg's lemma gives a torsion-free subgroup
  `H <= Gamma` of finite index; `H` inherits cocompactness, hyperbolicity,
  finite presentation and property (T).
- **Non-elementarity.**  `H` is infinite (it is a cocompact lattice in a
  noncompact group) and is not virtually cyclic (its symmetric space has
  dimension greater than one, and a virtually cyclic group has two ends), so it
  is non-elementary hyperbolic, hence acylindrically hyperbolic with trivial
  finite radical.

The alternative supply is Gromov's random groups at density
`1/3 < d < 1/2`, which are hyperbolic, torsion-free and Kazhdan for the density
model; that route is recorded as an alternative rather than the primary one,
because its property-(T) half rests on the spectral criterion literature whose
early accounts required subsequent clarification, whereas the lattice route is
uncontested.

**Degeneracy guard.**  The witness must be checked to be infinite before it is
used.  A finite group satisfies "torsion-free, hyperbolic, Kazhdan, finitely
presented" only by being trivial, and would discharge the literal sentence
while supplying nothing; the lattice above is infinite by construction.
