---
rg: 2
id: agent-stw77-zero-type-i-properness-does-not-descend-proof
kind: route
title: Infinitely amplify the finite Toeplitz--Cuntz defect
target: agent-stw77-zero-type-i-properness-does-not-descend
requires: []
---

Let `B=T_2` be the Toeplitz--Cuntz algebra in its faithful Fock
representation on the full Fock space `H_F`.  Write `v_1,v_2` for its
canonical isometries with orthogonal ranges and put

```text
e=1-v_1v_1^*-v_2v_2^*.
```

In the Fock representation `e` is the rank-one projection onto the vacuum.
The compact operators form the canonical ideal of `T_2`, and

```text
e T_2 e = C e.                                         (1)
```

Hence `e` is a nonzero finite projection in `T_2`.  On the other hand the
orthogonal isometries `v_1,v_2` show that `1_(T_2)` is properly infinite.

Now infinitely amplify the Fock representation:

```text
H=H_F tensor l2,
pi(b)=b tensor 1_(l2).                                 (2)
```

This representation is faithful and essential.  If `b!=0`, then
`b tensor 1_(l2)` is not compact: fix a vector on which `b` is nonzero and
apply it to an orthonormal sequence in the second tensor factor.  Therefore

```text
pi(T_2) intersect K(H)=0.                              (3)
```

Set

```text
D=C e + C(1-e) subset T_2.
```

This is a unital two-dimensional C-star algebra.  Both minimal projections
of `pi(D)` have infinite rank: `pi(e)=e tensor 1_(l2)` has countably infinite
rank, and so does its complement.  Infinite-rank projections in `B(H)` are
properly infinite.  Thus `pi(D)` is already a proper-support
finite-dimensional model inside `pi(T_2)`.

Take the scalar map

```text
phi:C->T_2,       phi(lambda)=lambda 1.
```

It has nuclear dimension zero, and every nonzero positive image is Cuntz
equivalent to the properly infinite unit.  Also

```text
(pi compose phi)(C)=C1 subset pi(D).
```

So both the finite-packet model error and the distance from `pi(D)` to a
finite-dimensional subalgebra of `pi(B)` are exactly zero.  Yet the inverse
image of the minimal projection `pi(e)` is the finite projection `e` by
`(1)`.  Proper infiniteness in `B(H)` therefore does not descend through the
faithful essential representation `(2)`.

The obstruction is not K-theoretic bookkeeping and not a poor perturbation
constant.  The type-I witnesses split the infinite multiplicity introduced
by the representation's `l2` factor; those shifts are absent from `T_2` at
the finite defect corner.  Any valid descent theorem must control these
witnesses, rather than only the finite-dimensional algebra they commute
with.
