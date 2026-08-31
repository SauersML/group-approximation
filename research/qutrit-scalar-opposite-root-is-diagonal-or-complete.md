---
rg: 2
id: qutrit-scalar-opposite-root-is-diagonal-or-complete
kind: claim
title: A scalar opposite root is diagonal or complete on the three qutrit phase sectors
artifacts:
  - research/qutrit-scalar-opposite-root-phase-graph-proof.md
distinct_from:
  qutrit-jacobson-residual-has-fixed-polar-gap: that gives the quantitative terminal if one complement branch is authenticated on the raw residual; this proves the scalar opposite root does not authenticate that branch pattern on the underlying qutrit phases.
  jacobson-pre-reduction-square-forces-sqrt-half-leakage: that quantifies how the opposite root leaves the raw residual; this computes its exact finite qutrit character-block graph.
  thompson-27-cylinder-qutrit-cell-is-fd-invisible: that constructs the three phase sectors in the prefix packet; this uses their explicit affine leaf action to classify every scalar transvection seam.
---

Let

```text
C=<J,Z_1> isomorphic to C_3^2,
e_a=z_(C,chi_a),        chi_a(J)=omega,
chi_a(Z_1)=omega^a,     a in F_3.
```

Then

```text
q=e_0+e_1+e_2,          R=e_0+e_1,          q-R=e_2.
```

Choose two distinct scalar coordinates among the 27 qutrit leaves and the
one extra coordinate, and let `k=1+E_ij` be the corresponding
characteristic-two transvection. Put

```text
H=C intersect kCk.
```

Exactly one of the following occurs.

1. If the two leaf coordinates have different `u_1`-labels, then
   `H={1}` and every block `e_b k e_a` is nonzero, with

```text
||e_b k e_a||_2^2=1/81                 for all a,b.     (QKG1)
```

2. If the leaf coordinates have the same `u_1`-label, or one coordinate
   is the extra fixed coordinate, then `H isomorphic to C_3`. The only
   nonzero blocks are diagonal:

```text
e_b k e_a=0 for a!=b,
||e_a k e_a||_2^2=1/27.                                (QKG2)
```

Thus the qutrit phase support graph of a scalar opposite root is either the
complete bipartite graph on the three phases or the diagonal matching. In
the first case `R` sees all three target phases; in the second it remains
separate from `q-R`. Neither case forces the two selected phases of
`R` through the single complement phase.

Consequently `x_31(1)` cannot by itself supply the one-complement
covariance needed by the residual qutrit gap. Any such selector must use the
raw residual compression jointly with a non-scalar `S/T` occurrence; it
is not already present in the finite scalar phase graph.
