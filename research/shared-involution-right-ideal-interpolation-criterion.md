---
rg: 2
id: shared-involution-right-ideal-interpolation-criterion
kind: claim
title: Shared involution interpolation is exactly one projection CRT
distinct_from:
  rowwise-shared-involution-forces-pairwise-marginal-closeness: that derives one necessary trace-distance inequality from the existence of a shared involution; this gives necessary and sufficient operator identities and constructs every solution.
  affine-frobenius-hecke-crt-shared-involution-interpolation: that asks for a finite-support canonical group-algebra realization with a strict deficit budget; this solves the Hilbert-space and finite-von-Neumann interpolation problem and isolates the remaining algebraic projection.
  common-meet-local-sectors-pay-one-deficit: that forms an intersection of row masks to transfer verifier energy; this does not intersect the masks and characterizes a unitary acting differently on their noncommuting right ideals.
---

**ESTABLISHED.**  Let `H` be a Hilbert space, let `q_1,...,q_r` be
orthogonal projections, and let `A_1,...,A_r` be self-adjoint unitaries.
Define row operators `X,Y:H^r -> H` by

```text
X(xi_1,...,xi_r)=sum_i q_i xi_i,
Y(xi_1,...,xi_r)=sum_i A_i q_i xi_i.                  (SIC1)
```

There exists a self-adjoint unitary `B` on `H` satisfying

```text
Bq_i=A_iq_i                    for every i             (SIC2)
```

if and only if

```text
X^*X=Y^*Y,                    X^*Y=Y^*X.               (SIC3)
```

Equivalently, for all `i,j`,

```text
q_i A_i A_j q_j=q_iq_j,
q_i(A_i-A_j)q_j=0.                                    (SIC4)
```

These are the complete pairwise compatibility equations; no higher
intersection condition is missing.

## Canonical reflection

Under `(SIC3)`, the closed subspaces

```text
E_+=closure ran(X+Y),             E_-=closure ran(X-Y) (SIC5)
```

are orthogonal.  If `e_-` is the projection onto `E_-`, then

```text
B_0=1-2e_-                                                (SIC6)
```

is a solution.  More generally, every solution is `1-2p`, where `p` is a
projection satisfying

```text
p(X+Y)=0,                     p(X-Y)=X-Y,               (SIC7)
```

or, equivalently,

```text
pq_i=[(1-A_i)/2]q_i             for every i.            (SIC8)
```

Thus shared-involution interpolation is literally a noncommutative Chinese
remainder problem for one projection `p` on several right ideals.

## Finite von Neumann versus algebraic realization

If all data lie in a finite von Neumann algebra `M`, then `e_-` is the range
projection of

```text
(X-Y)(X-Y)^*=sum_i (q_i-A_iq_i)(q_i-q_iA_i),           (SIC9)
```

so `B_0 in M`.  Hence the Gram equations `(SIC4)` completely solve the
finite-von-Neumann interpolation problem.

If instead the data lie in a unital star-subalgebra `R subseteq M`, an
algebraic solution `B in R` exists exactly when `(SIC8)` has a projection
solution `p in R`.  The support projection `e_-` need not belong to `R`.
For example, functional calculus always constructs it in the von Neumann
closure, but finite support requires an algebraic spectral separator (or a
different algebraic projection satisfying `(SIC7)`).

The same obstruction survives Julia/unitary stabilization.  A self-adjoint
unitary `Btilde in M_n(R)` which sends the fixed first-copy columns
`iota q_i` to `iota A_iq_i` yields the algebraic projection

```text
ptilde=(1-Btilde)/2 in M_n(R),
ptilde iota q_i=iota[(1-A_i)/2]q_i.                   (SIC10)
```

Conversely such a projection gives the stabilized reflection.  Therefore a
Julia completion can supply unused complement space, but it cannot replace
the required (possibly stabilized) algebraic projection CRT.

## Compressed masks do not help when the masks reduce the marginals

Put `e_i=(1-A_i)/2`.  The compressed equations

```text
q_i(B-A_i)q_i=0                                        (SIC11)
```

are equivalent to `q_i p q_i=q_i e_iq_i`.  If
`[q_i,A_i]=0`, as for the private central Frobenius block masks, then
`e_iq_i` is a projection.  A compression `q_i p q_i` of a projection is a
projection only when `p` commutes with `q_i`.  Hence `(SIC11)` forces

```text
pq_i=q_ip=e_iq_i,                                      (SIC12)
```

which is exactly the original one-sided equation.  Passing to compressed
agreement gives no extra interpolation freedom for the intended reducing
masks.
