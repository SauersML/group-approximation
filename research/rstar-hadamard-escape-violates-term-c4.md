---
rg: 2
id: rstar-hadamard-escape-violates-term-c4
kind: claim
title: An R-star Hadamard escape makes each separated subdivided endpoint pairing a two-piece relator
distinct_from:
  overlap-subdivision-preserves-coherent-piece-obstruction: that rules out C-prime one-sixth for every recurrent four-potential endpoint contour and leaves exotic C(4)-T(4) open; this uses the odd-parity geometry of R-star and the explicit rank-two escape to refute C(4) for the separated term-pairing architecture.
  one-binary-marginal-block-escape: that constructs the rank-two Hadamard/free-phase escape while preserving one sign; this tracks the other R-star marginals and audits their coefficient relators.
---

Let

```text
R_*={a in F_2^4: sum_x a_x=1}\{1000}.                  (RHC1)
```

Use the explicit cell of `one-binary-marginal-block-escape` on two rank-one
coordinates `r,s` belonging to distinct assignments `a,b in R_*`.  Assume
the cell preserves marginal `x`, so `a_x=b_x`, and write `h_r,h_s` for its
free phase generators.  Then the escaped assignment projections have, on
the `(r,s)` plane,

```text
P_a = (e_r+e_s+h_r h_s^(-1)E_rs+h_s h_r^(-1)E_sr)/2,
P_b = (e_r+e_s-h_r h_s^(-1)E_rs-h_s h_r^(-1)E_sr)/2.  (RHC2)
```

(The displayed formula suppresses the unchanged orthogonal summands of the
two coarse assignment projections.)  Hence for the signed marginal
`X_y=sum_c (-1)^(c_y)P_c`, the coefficient of

```text
h_r h_s^(-1)E_rs                                         (RHC3)
```

is

```text
((-1)^(a_y)-(-1)^(b_y))/2.                              (RHC4)
```

No other assignment atom contributes to this matrix entry, so this term
cannot cancel inside `X_y`.

All points of `R_*` have the same odd parity.  Therefore two distinct
points have positive even Hamming distance.  Since `a_x=b_x`, they differ in
at least two coordinates `y!=z`, both different from `x`.  By `(RHC4)`, the
same full group-ring support term `(RHC3)` occurs, up to coefficient sign,
in both `X_y` and `X_z`.  After expanding the fixed matrix unit `E_rs` in
the finite packet group, every individual support word with nonzero
coefficient has the same recurrence property.  This is recurrence of the
**whole term**, not merely of one phase subword.

Now synchronize all logical marginals by coefficient term pairing and
subdivide the consistency edges by genuine equality chains of length at
least two, using disjoint potential alphabets at consecutive vertices.  An
endpoint term-pairing relator has cyclically reduced form

```text
u v^(-1),                                                (RHC5)
```

where `u` is one of the full support words just described and `v` is the
paired term at the first intermediate equality vertex.  The word `u` is a
piece because it occurs in the distinct `y`- and `z`-marginal pairing
relators (inverse orientation is allowed after symmetrization).  The word
`v` is a piece because the same intermediate observable participates in
the two adjacent segment equalities.  Disjoint consecutive alphabets ensure
that the two arcs survive cyclic reduction.  Thus `(RHC5)` is a product of
two pieces and violates ordinary graphical `C(4)`, as well as any relative
`C(4)` formulation in which the two paired full terms survive as distinct
nonperipheral arcs (the standard separated-potential term presentation has
this property).  If all potential and coefficient words are instead
absorbed into one peripheral factor, the relator lies in that factor and no
relative Freiheitssatz protects it; this is not an escape from the
obstruction.

The same conclusion holds without a length-two subdivision if the term at
the other endpoint is itself recurrent as a full term.  A longer macro
cycle cannot change this local two-piece factorization, so `T(4)` never
enters.

This is deliberately a statement about the explicit rank-two
Hadamard/free-phase cell and coefficientwise synchronization of every
marginal.  It does not exclude a block escape whose marginal coefficients
cancel across several planes, an aggregate non-termwise equality, or a
different source relation containing Hamming-distance-one assignment pairs.
Those are the remaining ways a genuine `C(4)-T(4)` design could avoid the
argument.
