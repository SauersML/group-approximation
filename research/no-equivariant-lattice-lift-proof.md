---
rg: 2
id: no-equivariant-lattice-lift-proof
kind: route
title: Dualize the lift to an equivariant retraction and push Haar measure onto the Cantor set
target: no-equivariant-lattice-lift-of-cylinder-idempotents
requires:
  - signed-thompson-algebra-is-odd-measure-crossed-product
artifacts:
  - research/artifacts/ternary-cohn-mixed-depth-lifts-2026-09-12.md
---

Section 3 of the artifact.
- Stone duality turns a Boolean homomorphism `Phi` into a continuous map `r : M_- -> X` with
  `Phi(C) = r^-1(C)`.
- Dirac compatibility gives `r(delta_x) = x`, and equivariance gives `r(g mu) = g r(mu)`.
- The Haar measure on `M_-` is `V`-invariant: restricted to the algebra of any prefix code it is uniform on
  odd functions, and `V` permutes the atoms of prefix-code algebras. So `r_* lambda` is a `V`-invariant
  probability measure on `X`.
- Prefix replacements `{0,10,11} -> {00,01,1}` and `{0,10,11} -> {01,00,1}` give `nu(0) = nu(00) = nu(01)`,
  hence `nu(0) = 0`, and the first-letter swap gives `nu(1) = 0`, contradicting `nu(X) = 1`.
