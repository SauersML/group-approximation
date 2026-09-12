---
rg: 2
id: code-laplacian-has-uniform-cp-green-approximants
kind: claim
title: The exact code Laplacian has uniform completely positive Green approximants
distinct_from:
  complete-overlay-row-newton-is-a-code-riesz-multiplier: that identifies the coordinate coboundary inverse as a vector-valued Riesz multiplier; this handles the scalar adjoint Laplacian by CP noise averages and does not claim that the gradient factor is completely bounded.
  complete-overlay-code-group-has-uniform-conjugation-gap: that proves the Hilbert--Schmidt spectral gap by character orthogonality; this packages its inverse into finite CP polynomials which also control operator row and column norms.
  balanced-overlay-diffuse-square-function-newton: that starts away from exact parity; this construction is at an exact code representation and isolates the perturbative extension still needed.
---

Let `Q_1,...,Q_L` be an exact representation of the complete-overlay code
group for a binary code of relative distance at least `delta`.  On the matrix
algebra define the ucp pinchings and their average

```text
E_i(X)=(X+Q_iXQ_i)/2,
A=(1/L)sum_i E_i,                 Delta=I-A.              (CLG1)
```

For every integer `K>=1`, the truncated Green operator

```text
G_K=sum_(t=0)^(K-1) A^t                                  (CLG2)
```

is a sum of `K` ucp maps, has completely bounded norm at most `K`, and is
contractive up to the same factor on every operator row and column
amplification.  It satisfies the exact polynomial identity

```text
G_K Delta=I-A^K.                                         (CLG3)
```

If `E` is the trace-preserving expectation onto the common commutant, then

```text
||(A^K-E)X||_2 <=(1-delta)^K||(I-E)X||_2.                (CLG4)
```

Thus for any target accuracy `eta`, choosing
`K=O_delta(log(1/eta))` gives an approximate inverse with cb row/column
cost depending only on `delta,eta`, never on code length, matrix dimension,
or character multiplicity.

The equality-expander Laplacian has the same structure.  After lazifying its
doubly stochastic Markov operator `P`, the polynomial
`sum_(t<K)P^t` is row/column contractive up to `K`, and its `L_2` inverse
error off constants is at most `(1-gamma)^K` for expander gap `gamma`.

This resolves the CP/contractive-average question for the adjoint code and
equality Laplacians.  It does **not** by itself invert the coordinate
coboundary: applying a gradient to `Delta^(-1)` produces precisely the code
Riesz multiplier isolated in
`complete-overlay-row-newton-is-a-code-riesz-multiplier`.  Nor does `(CLG4)`
hold in cb norm; it is the `L_2` contraction used alongside the bounded cb
size of `G_K`.
