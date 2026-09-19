---
rg: 2
id: adjoint-parity-cone-lifts-to-loewner-order
kind: claim
title: Exact parity lifts the Tanner fundamental cone to Loewner order on Hilbert--Schmidt space
distinct_from:
  adjoint-parity-defects-form-tanner-fundamental-cone: that proves scalar norm inequalities after choosing one Hilbert--Schmidt vector; this proves the underlying positive-operator inequalities simultaneously for every vector and imports every max-fractional cone bound in Loewner order.
  commutator-threshold-sets-need-not-be-stopping-sets: that refutes thresholding the scalar magnitudes coordinate by coordinate; this gives the valid replacement, domination by one row-average positive operator without choosing incompatible thresholds.
  central-clifford-parity-sectors-round-uniformly: that rounds scalar-sign commutator sectors completely; this applies to arbitrary noncentral commutators but yields alignment and magnitude spreading rather than an exact correction.
---

Let `Q_1,...,Q_L` be reflections in a finite tracial von Neumann algebra.
Assume that in each check `T` they commute and have product `I`.  On
`L_2(M)` define the orthogonal projections

```text
P_i=(I-Ad(Q_i))/2.                                        (APL1)
```

Then for every check `T` and `i in T` one has the positive-operator
inequality

```text
P_i <= sum_(k in T, k!=i) P_k.                            (APL2)
```

Consequently every homogeneous linear inequality that is valid on the
Tanner fundamental cone lifts, after moving its negative-coefficient terms
to the other side, to Loewner order for `(P_i)`.  In particular, if the chosen code family has uniform
max-fractional pseudodistance `kappa L`, so that every cone vector obeys

```text
x_i <= (1/(kappa L)) sum_k x_k,                           (APL3)
```

then

```text
P_i <= (1/(kappa L)) sum_k P_k.                           (APL4)
```

Applying `(APL4)` to `Q_j in L_2(M)` gives the arbitrary-noncentral
commutator estimate

```text
||Q_iQ_j-Q_jQ_i||_2^2
 <= (1/(kappa L)) sum_k ||Q_kQ_j-Q_jQ_k||_2^2.            (APL5)
```

This row estimate self-improves, by symmetry, to a uniform bound from the
complete-pair average.  If

```text
E_com=(1/L^2)sum_(a,b)||Q_aQ_b-Q_bQ_a||_2^2,
```

then

```text
max_(i,j)||Q_iQ_j-Q_jQ_i||_2^2 <= E_com/kappa^2.          (APL6)
```

Indeed, one application of `(APL5)` makes the sum of row `i` at least
`kappa L` times its `(i,j)` entry.  For each entry in that row, a second
application makes the corresponding full row sum at least `kappa L` times
that entry.  Summing gives total matrix mass at least `kappa^2 L^2` times
the original entry.

Thus exact parity forbids the proposed spectral-partner reservoir: a large
commutator in one pair cannot be paid by mutually incompatible partners on
tiny character pieces without making the whole commutator row large.  This
statement does not centralize the commutators and does not prove basin
capture.  A remaining countermodel may have every pair commutator uniformly
small in normalized Hilbert--Schmidt norm while its order-one operator-norm
spectral cuts move with the pair.  Controlling a common approximately
reducing cut for those diffuse noncentral remainders is still exactly
`complete-pair-overlay-uniform-hs-basin-capture`.
