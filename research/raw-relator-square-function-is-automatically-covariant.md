---
rg: 2
id: raw-relator-square-function-is-automatically-covariant
kind: claim
title: The raw relator square function is automatically HS-covariant
distinct_from:
  covariant-square-function-has-common-reducing-threshold: that converts covariance into a spectral cut; this supplies its covariance hypothesis directly from mean squared defect
  complete-pair-overlay-uniform-hs-basin-capture: that needs coordinate operator-norm proximity to an exact representation; this yields only a bounded normalized row-residual operator on the retained corner
---

Let `(R_a)_(a in A)` be arbitrary matrix residuals with
`||R_a||_op<=2`, and put

```text
 H=(1/|A|) sum_a R_a^*R_a,
 epsilon=tau(H).                                         (RSC1)
```

For every unitary `U`, without any permutation or conjugacy symmetry of the
residual family,

```text
 ||[H,U]||_2 <=4 sqrt(epsilon).                          (RSC2)
```

Indeed `||[X,U]||_2<=2||X||_2`,
`||R_a^*R_a||_2<=2||R_a||_2`, and Cauchy--Schwarz in the uniform `a`
average proves `(RSC2)`.

Thus `covariant-square-function-has-common-reducing-threshold` applies to
the raw balanced-overlay residual square function and gives one common
almost-reducing high-energy cut of vanishing trace.  Covariance is not the
remaining basin obstruction.

On the retained projection `q`, a threshold at height `b` gives only

```text
 qHq <= bq.
```

This bounds the normalized operator row of all residuals.  It does not bound
each residual in operator norm without a factor depending on `|A|`, and it
does not put the coordinate tuple in operator distance of an exact
representation.  The remaining gate is therefore a uniform row-residual-
to-coordinate-tube theorem.
