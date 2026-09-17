---
rg: 2
id: torus-automata-with-regular-degree-are-surjective
kind: claim
title: Over every group, a continuous equivariant self-map of a torus full shift whose degree matrix is regular over Q[G] is surjective
distinct_from:
  stable-finiteness-forces-binary-surjunctivity: that is a conditional finite-alphabet statement over F_2; this is an unconditional statement for connected torus alphabets, proved by topological degree, for maps that need not be injective or linear.
  homomorphic-codes-cannot-compress-bernoulli-shifts: that restricts homomorphic codes by a kernel element on constants; this controls arbitrary nonlinear continuous maps through their action on first cohomology.
artifacts:
  - research/artifacts/torus-alphabet-degree-2026-09-17.md
---

Let `G` be a countable group, `d >= 1`, `T = R/Z`, and `tau: (T^d)^G -> (T^d)^G` any
continuous `G`-equivariant map. No finite memory, injectivity or linearity is assumed.

- **Degree matrix.** Čech `H^1((T^d)^G; Z) = Z[G]^d`. The pullback `tau^*` is a
  `Z[G]`-module endomorphism of this free module, `xi -> xi D` with
  `D = D(tau) in M_d(Z[G])`.
- **Claim.** If `xi -> xi D` is injective on `Q[G]^d`, then `tau` is surjective.

Equivalently, a torus automaton is onto whenever its linearization, the linear automaton
with the same matrix, is onto.

**ESTABLISHED 2026-09-17** by [[torus-automata-with-regular-degree-are-surjective-proof]].

## Attempts

- 2026-09-17 (swarm-0917-w4-gs-decomp-new): proof in Section 1 of the artifact.
  - Pick a nonzero `dF x dF` minor on a finite window.
  - Restrict `tau` to the slice of those input coordinates.
  - The slice map is a map of tori of degree `+- det != 0`, so it is onto.
  - Compactness gives global surjectivity.
