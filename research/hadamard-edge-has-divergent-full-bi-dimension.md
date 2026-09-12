---
rg: 2
id: hadamard-edge-has-divergent-full-bi-dimension
kind: claim
title: Exact Hadamard edge models have divergent bi-dimension on a full carrier
distinct_from:
  canonical-moments-admit-divergent-edge-leakage: That uses small rotations to make an unnormalized principal-angle sum diverge while each fixed covariance defect vanishes; this gives an exact single-correspondence model whose left and right module dimensions themselves diverge and whose carrier is all of the matrix algebra.
  kt-literal-return-stays-far-from-edge-normalizers: That proves the literal Kun--Thom return is separated from every edge normalizer; this calibration simultaneously has that separation and divergent full-support correspondence dimensions, showing those facts are compatible in finite matrices.
  marked-double-coset-infinite-degree: That computes an infinite group double-coset degree; this is a finite-dimensional matrix calibration showing that unbounded correspondence degree has no normalized-rank cost by itself.
---

For every `d=2^r` there is a unital edge algebra `D_d subset M_d` and a
self-adjoint unitary `H_d` such that

```text
closure(D_d H_d D_d)=M_d,                              (HBD1)
dim_(D_d)^right(M_d)=dim_(D_d)^left(M_d)=d,             (HBD2)
||E_(D_d)(H_d)||_2=d^(-1/2).                           (HBD3)
```

Thus the two correspondence dimensions diverge while the correspondence has
full physical density in `L2(M_d)` and the return expectation vanishes.

The calibration also realizes the fixed mixed-word geometry.  There is a
trace-zero involution `a_d in D_d` with

```text
E_(D_d)(H_d^* a_d H_d)=0.                              (HBD4)
```

Consequently `H_d` stays at normalized-HS distance at least `1/2` from the
normalizer of `D_d`, even though its generated left/right correspondence is
the whole ambient matrix algebra.  Subtracting `E_(D_d)(H_d)` and taking a
closest unitary polar extension changes `H_d` by at most `2/sqrt(d)`, so all
four features survive the correction used for the Kun--Thom returned edge:

```text
vanishing return expectation,
one exact exterior-conjugate test,
divergent equal left/right dimensions,
full physical carrier.                                 (HBD5)
```

Therefore neither divergent bi-dimension, a left/right dimension comparison,
full support, nor their conjunction with the current mixed expectation tests
can yield a finite-matrix obstruction.  The missing Kun--Thom content remains
compatibility with the full actor and its strict compressor relations.

DERIVATION
walsh-hadamard-full-correspondence-proof
