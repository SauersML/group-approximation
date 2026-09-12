---
rg: 2
id: finite-spectrum-integral-elements-obey-determinant
kind: claim
title: Over every group, integral self-adjoint matrices with finite spectrum have Serre-class spectral measures
invalidates:
  - determinant-counterexample-via-galois-unequal-atoms
distinct_from:
  atomic-serre-measures-are-equal-weight-real-orbits: that characterizes the finitely atomic Serre-class measures and has no group in it; this proves that every finite-spectrum integral group-ring spectrum, over every group, is such a measure
  determinant-conjecture-holds-for-sofic-groups: that proves the conjecture for sofic groups by approximation; this proves it for one class of matrices over every group, nonsofic included, with no approximation
  kun-thom-wreath-galois-unequal-atomic-element: that asked for a finite-spectrum witness with Galois-unequal masses; this shows no group has one
  determinant-violation-needs-nonsofic-support-subgroup: that localizes a violation to a nonsofic support subgroup; this forces the violating spectrum to be infinite, whatever the group
---

**ESTABLISHED** by `finite-spectrum-integral-determinant-proof`.

Let `G` be any group and let `A in M_n(Z[G])` be self-adjoint, acting by right
multiplication on `l^2(G)^n`, with finite spectrum. Write `mu_A` for its
spectral measure with respect to `Tr = sum_i tau(X_ii)`. Then:

1. `sigma(A)` is the root set of a squarefree monic `m in Z[x]` with
   `m(A) = 0` in `M_n(Z[G])`. So it is a Galois-stable set of totally real
   algebraic integers.
2. Every mass `mu_A({lambda})` is rational.
3. Galois-conjugate eigenvalues carry equal mass.
4. `integral_{Q != 0} log |Q| d mu_A >= 0` for every nonzero `Q in Z[x]`.

In particular `det_N(G)(B) >= 1` for every `B in M_{m x n}(Z[G])` such that
`B^* B` has finite spectrum.

**Consequences for the determinant conjecture.**

- **Violations need infinite spectrum.** The finitely atomic shape of
  `integer-moment-measure-with-negative-log-determinant`, realized as unequal
  von Neumann multiplicities, is impossible over every group. This refutes
  `kun-thom-wreath-galois-unequal-atomic-element` and kills
  `determinant-counterexample-via-galois-unequal-atoms`.
- **What replaces soficity.** In the Elek--Szabó proof, integrality survives
  approximation. Here Zalesskii's characteristic-`p` trace argument does the
  same job, with no approximation of `G`, but only for elements algebraic over
  `Q`.
- **Residual shapes.**
  - Infinite spectrum with algebraic atoms of unequal conjugate mass. An
    isolated atom `lambda` has `E_lambda` in `C*_r(G)` rather than in
    `K[G]`, so Zalesskii no longer applies.
  - Too much spectrum near `0`, the Strong Atiyah shape of
    `determinant-counterexample-from-atiyah-counterexample`.
