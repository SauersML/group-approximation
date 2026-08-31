---
rg: 2
id: pauli-swap-coherence-reduces-to-the-commutant-gate
kind: claim
title: A two-sheet Pauli swap cannot carry the Jacobson head
distinct_from:
  bounded-coherence-toeplitz-gauges-cannot-retain-head: that starts with commutant-valued gauges; this removes the first genuinely off-diagonal normalizer extension
  presentation-defect-does-not-control-off-commutant-mass: that shows arbitrary off-commutant size is uncontrolled; this uses the discrete two-sheet structure to recover rigidity
  unbounded-commutant-coherence-is-the-original-gate: that classifies the remaining diagonal coherence after the swap parity is eliminated
---

Let `G=EL_28(J)` with its fixed finite presentation
`P=<Sigma | R>`. On a decomposition `H=H_0 directSum H_1` with equal
summand dimensions, suppose the carrier matrices

```text
A_s=rho(theta_N(s))
```

are block diagonal. Let `X` be a fixed unitary swapping `H_0` and `H_1`.
Consider the smallest Pauli-normalizer gauges

```text
Z_s=D_s X^(epsilon_s),          epsilon_s in {0,1},      (PSC1)
```

where every `D_s` is block diagonal and lies in `rho(F_N)'`. Put
`U_s=A_sZ_s`.

If

```text
delta(U)=max_(r in R)||r(U)-I||_2 < sqrt(2),             (PSC2)
```

then `epsilon_s=0` for every generator `s`. Hence every gauge in `(PSC1)`
already lies in the carrier commutant.

Consequently no head-retaining microstate can be created by adding one
global Pauli swap sheet to the Toeplitz carrier. With bounded isotypic
multiplicity, the head then collapses by
`bounded-coherence-toeplitz-gauges-cannot-retain-head`. With unbounded
multiplicity, the construction is exactly the original Jacobson gate by
`unbounded-commutant-coherence-is-the-original-gate`.

The threshold is dimension-free and does not use an expansion estimate.
It comes from the exact orthogonality of block-diagonal and block-
off-diagonal matrices together with the perfectness of `EL_28(J)`.

This theorem covers monomial Pauli motion `D_sX^(epsilon_s)`. It does not
cover a coherent superposition with simultaneously nonzero diagonal and
off-diagonal blocks, nor generator-dependent moving decompositions. Those
continuous rotations are the smallest surviving mixed-isotype ansatz.

DERIVATION
perfectness-kills-the-two-sheet-pauli-parity-proof
