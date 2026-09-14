---
rg: 2
id: level15-strong-atiyah-via-extended-parity-character
kind: route
title: An invariant parity character on the units of D_C(N) kills the norm equation for the level-15 lattice
target: level15-torsion-free-lattice-satisfies-strong-atiyah
requires:
  - sl3z-level-15-torsion-free-subgroup-outside-p-adic-hosts
  - twisted-norm-equation-dies-under-invariant-parity-character
  - level15-parity-character-extends-to-linnell-division-ring
---

`H` is torsion-free, and `N = H cap Gamma(3)` has index 2 and satisfies Strong Atiyah over
`C` (item 2 of [[sl3z-level-15-torsion-free-subgroup-outside-p-adic-hosts]]). The
character supplied by [[level15-parity-character-extends-to-linnell-division-ring]]
satisfies the hypotheses of
[[twisted-norm-equation-dies-under-invariant-parity-character]] with `K = C`, so `H`
satisfies Strong Atiyah over `C`.
