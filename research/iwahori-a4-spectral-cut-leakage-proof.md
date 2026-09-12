---
rg: 2
id: iwahori-a4-spectral-cut-leakage-proof
kind: route
title: Compute a tetrahedral residual energy and dilute a nonreducing spectral line
target: iwahori-spectral-cuts-need-independent-leakage-control
requires: []
artifacts:
  - research/artifacts/iwahori-spectral-threshold-leakage-counterexample-2026-09-08.md
---

Set `S=diag(1,-1,-1)`, let `B` cycle the three coordinate vectors,
and use the compatible modular pair `(S,B,S,BSB)`. Conjugate only its
first `S` by rotation through `t` in the first two coordinates. The
artifact computes the two Iwahori residuals exactly and obtains

```text
sum_j R_j(t)^*R_j(t)/(4t^2)
  --> [ 2 -1 0 ; -1 1 0 ; 0 0 3 ].
```

Its eigenvalues are `(3-sqrt(5))/2`, `(3+sqrt(5))/2`, and `3`.
The spectral cut at `11t^2` therefore has rank one and converges to
the third-coordinate projection. Leakage under `B` tends to one in
Frobenius norm. Fix a sufficiently small nonzero `t` and adjoin
trivial coordinates. The cut's threshold is now fixed and positive,
and both normalized-HS defect and nonzero leakage scale by `n^(-1/2)`.
Their ratio stays positive, proving the stated obstruction.

The commutator Frobenius norm tends to `sqrt(2)`, and the residual
Hilbert tuple Frobenius norm is asymptotic to `sqrt(24)t`.
Since `theta=11t^2`, their ratio is asymptotic to
`sqrt(11/12)/sqrt(theta)`, independently of the dilution dimension.
For all sufficiently small fixed thresholds, this forces
`4L kappa_2>e/2>=e_max/2` with `L=6`, where `e` is the Hilbert
tuple defect and `e_max` is the maximum residual norm. The raw cut
therefore fails the support-erasure sufficient contraction budget,
regardless of its nonnegative retained-residual term.

The same calculation makes the full residual support the whole
three-dimensional block. Undoing the first conjugation restores the
displayed endpoint with movement at most the defect divided by
`sqrt(2)`. Thus the argument establishes only the claimed failure of
automatic relative leakage for the specified spectral cut.
