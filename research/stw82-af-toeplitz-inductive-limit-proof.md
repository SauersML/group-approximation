---
rg: 2
id: stw82-af-toeplitz-inductive-limit-proof
kind: route
title: Tensor the scalar Toeplitz colours through finite-dimensional AF stages
target: stw82-af-coefficient-toeplitz-maximum
requires:
  - stw82-raw-two-cut-reuse-iff-quasidiagonal
---

## Exactness and the endpoint dimensions

The scalar algebra `T_N` fits into the essential extension

```text
0 -> K -> T_N -> C(T) -> 0,                            (3)
```

where the quotient sends `S^N` to the coordinate unitary and the boundary
index of that unitary is `+-N`.  Since `A` is nuclear, minimal tensoring
preserves (3), giving `(AF-T)`.

The ideal `K tensor A` is AF and therefore has nuclear dimension zero.
Write `A` as an increasing unital inductive limit of finite-dimensional
algebras

```text
A_j=directSum_l M_(n(j,l)).
```

Then

```text
C(T) tensor A
 = lim_j directSum_l M_(n(j,l))(C(T)).                 (4)
```

Matrix stability, finite-direct-sum permanence, and inductive-limit
permanence give nuclear dimension at most one.  It is not zero: the
Kunneth formula, with the free `K`-groups of `C(T)`, gives

```text
K_1(C(T) tensor A)=K_0(A),                             (5)
```

and this group contains the nonzero order unit `[1_A]`, whereas a separable
AF algebra has zero `K_1`.  Since separable nuclear-dimension-zero algebras
are AF, (5) proves the second equality in (1).

## The middle algebra

The scalar index-`N` Toeplitz algebra has nuclear dimension one.  This follows
either by the scalar Brake--Winter transition-band construction, unchanged
for the rank-`N` defect, or from the dimension-one theorem for essential
extensions of a commutative algebra by `K`.  Therefore

```text
T_N tensor A_j
 =directSum_l M_(n(j,l))(T_N)
```

has nuclear dimension one for every `j`.  The injective inductive limit over
the AF stages gives

```text
dim_nuc(T_N tensor A)<=1.                              (6)
```

Its quotient in `(AF-T)` has nuclear dimension one, so quotient monotonicity
turns (6) into equality.  This proves all of (1).

## Why raw-cut reuse is unavailable

Naturality of the six-term exact sequence under exterior product with
`[1_A]` carries the scalar index in (3) to

```text
partial([z] tensor [1_A])=+-N[1_A].
```

The ordered `K_0` group of a unital AF algebra is torsion free and its order
unit is nonzero, so this class does not vanish.  A quasidiagonal extension
has zero index boundary: compression by a quasicentral approximate unit of
projections gives finite-corner lifts of quotient unitaries and kills their
Fredholm index.  Hence `(AF-T)` is not quasidiagonal.  The equivalence in
`stw82-raw-two-cut-reuse-iff-quasidiagonal` then rules out asymptotic
orthogonalization of the raw complementary supports.  The dimension-one
bound is supplied instead by the coherent scalar Toeplitz approximations at
the finite-dimensional coefficient stages.
