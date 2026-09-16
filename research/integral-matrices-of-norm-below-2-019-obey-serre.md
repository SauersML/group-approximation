---
rg: 2
id: integral-matrices-of-norm-below-2-019-obey-serre
kind: claim
title: Over every group a self-adjoint integral matrix of norm below 2.019 splits into a finite-spectrum part and a part of norm at most two, obeys every Serre inequality, and has norm at most two or one of ten McKee--Smyth values
distinct_from:
  norm-two-integral-matrices-reduce-to-virtually-cyclic-groups: that stops at norm two; this passes two, where finite noncyclotomic components appear, and shows they are the only new thing up to 2.019
  integral-operator-norm-below-two-is-quantized: that quantizes norms below two as 2cos(pi/q); this quantizes norms in (2, 2.019) to ten algebraic values attained on finite components
  tripod-free-integral-matrices-reduce-to-virtually-cyclic: that bounds the absolute norm |A| and allows no cancellation; this bounds the signed norm, so |A| may have large norm, as for signed tessellations
  small-spectral-radius-integer-matrices-classified: that is the finite-matrix classification; this is its consequence for group-ring operators
artifacts:
  - research/artifacts/determinant-norm-room-2026-09-16.md
---

**ESTABLISHED** by `integral-matrices-norm-below-2-019-serre-proof`. Unreviewed.

Let `G` be any group and `A in M_n(Z[G])` self-adjoint with `||r_A|| < 2.019`.
Let `Gamma_A` be the graph of nonzero off-diagonal entries of `r_A` on
`G x [n]`.

1. **Infinite components are cyclotomic.** On every infinite component of
   `Gamma_A`, `r_A` has norm at most `2`.
2. **Splitting.** Say `j in [n]` is finite or infinite according to the
   component of `(e, j)`. After permuting indices,
   `A = A_fin (+) A_inf` with `mu_A = mu_(A_fin) + mu_(A_inf)`. Here `r_(A_fin)`
   has finite spectrum, and `||r_(A_inf)|| <= 2`.
3. **Serre.** `det_N(G) r_(Q(A)) >= 1` for every nonzero `Q in Z[x]`.
   Eigenvalues are algebraic integers, and conjugates carry equal mass.
4. **Quantization.** `||r_A||` is at most `2`, or equals one of
   `2.00659, 2.00960, 2.01076, 2.01348, 2.01532, 2.01658, 2.01746, 2.01809,
   2.01854, 2.01887` (rounded). In the second case it is attained on a finite
   component equivalent to one of the seventeen McKee--Smyth graphs.

**Reading.** Up to `2.019`, a signed integral operator can pass norm two only
through finite noncyclotomic pieces, and it still cannot violate a Serre
inequality. Past `2.0198...`, finite noncyclotomic pieces of unbounded size
exist. The signed range `(2.019, 3/sqrt 2)` is open
(`integral-matrices-of-norm-below-3-over-sqrt2-obey-serre`).
