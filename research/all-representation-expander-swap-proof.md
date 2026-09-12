---
rg: 2
id: all-representation-expander-swap-proof
kind: route
title: Compute the partial trace and commutators of tensor flip
target: all-representation-expansion-keeps-macroscopic-multiplicity-swap
requires: []
---

Use normalized matrix traces throughout and write

```text
F=sum_(i,j) e_ij tensor e_ji.
```

Then `F=F^*=F^(-1)` and `F(a tensor b)=(b tensor a)F`.  Taking `a=b=V_i`
proves the first equality of `(UES1)` for arbitrary unitary checks, without
any hypothesis on their gap.

The trace-preserving conditional expectation onto `I_d tensor M_d` sends
`e_ij tensor e_ji` to `delta_ij I_d tensor e_ii/d`.  Summing gives
`E(F)=I_(d^2)/d`.  Since conditional expectation is the Hilbert-space
orthogonal projection in normalized `L^2`,

```text
dist_2(F,I_d tensor M_d)^2
 =||F||_2^2-||E(F)||_2^2
 =1-1/d^2.
```

Moreover

```text
[F,a tensor I]=((I tensor a)-(a tensor I))F,
||[F,a tensor I]||_2^2
 =2-2|tr_d(a)|^2
```

for a unitary `a`.  This proves `(UES2)`.  Traceless unitaries exist in
every dimension `d>=2`, for example the diagonal matrix of all `d`th roots
of unity.  The two swap eigenspaces have dimensions `d(d+1)/2` and
`d(d-1)/2`; the obstruction has macroscopic normalized mass.

If `V_i in SU(d)`, the map

```text
rho(V)=Ad(V tensor V) on L^2(M_(d^2))
```

is a continuous unitary representation and `rho(V)F=F` for every `V`.
Thus even a spectral-gap theorem quantified over all such representations
does not bound this vector by its generator displacements.  The theorem
applies only after projecting away *all* invariant vectors, which include
`F`; projecting only onto `I_d tensor M_d` is a different operation.

Finally, unitary invariance and the triangle inequality give

```text
||[F,D_i]||_2
 =||[F,D_i-V_i tensor V_i]||_2
 <=2||D_i-V_i tensor V_i||_2.
```

This supplies the perturbation claim.  The same example refutes any proposed
estimate with a right-hand side converging to zero with the check defects,
even in one fixed dimension, and uniformly as the dimension increases.
