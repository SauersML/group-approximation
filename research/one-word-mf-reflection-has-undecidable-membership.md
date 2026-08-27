---
rg: 2
id: one-word-mf-reflection-has-undecidable-membership
kind: claim
title: A one-word internal MF reflection has undecidable subgroup membership
root: true
artifacts:
  - research/mihailova-one-word-internal-reflection-proof.md
---

There are fixed finitely generated groups

```text
K<=P<=U=L_(F_2)(1,2)^x                               (MUR1)
```

such that membership in `K` is undecidable for words in the generators of
`P`, and hence also for the corresponding words in a fixed finite generating
set of `U`.  Both ambient groups `P` and `U` have decidable word problem, so
this is an undecidable generalized word problem inside groups whose own word
problem is decidable.  The group `K` is non-MF and has a split quotient

```text
pi:K->>T                                               (MUR2)
```

with

```text
Rad_MF(K)=ker(pi)=normalClosure_K(d)                   (MUR3)
```

for one explicit involution `d`.  The visible group `T` is finitely
generated, torsion-free, residually a finite `2`-group, and linear in
characteristic zero.

Precomposition with `pi` gives natural bijections

```text
Hom(T,M)~=Hom(K,M)                                     (MUR4)
```

for every MF group, finite group, compact group, finite-dimensional unitary
group, and finite-dimensional linear group over every field.  Therefore the
MF, finite, compact, unitary, and all-field linear residuals of `K` all equal
the one-word kernel in `(MUR3)`, and

```text
profiniteCompletion(K)~=profiniteCompletion(T),
Bohr(K)~=Bohr(T).                                      (MUR5)
```

The same kernel is also the finite-`2`, nilpotent, and solvable residual and
has the intrinsic descriptions

```text
ker(pi)=intersection_j lowerCentral_j(K)
       =intersection_j derived_j(K).                   (MUR5a)
```

The pro-`2`, pronilpotent, and prosolvable completions of `K` are canonically
those of `T`.

Every finite-index subgroup of `K` contains `ker(pi)`.  Hence inverse image
under `pi` is an inclusion-, index-, core-, and conjugacy-preserving
isomorphism from the entire finite-index subgroup lattice of `T` onto that of
`K`.  In particular, `K` and `T` have equivalent categories of finite
actions, not merely isomorphic profinite completions.

In particular, `K` is neither residually finite, maximally almost periodic,
nor linear over any field, although dimension by dimension and field by
field its entire finite-dimensional representation functor is the pullback
of that of the residually finite linear group `T`.

For every normal subgroup `N` of `K`, the full semantic closure is

```text
cl_MF^K(N)=pi^(-1)(cl_MF^T(pi(N))).                    (MUR6)
```

Thus the undecidable subgroup-membership phenomenon occurs inside one fixed
finitely generated matrix group while its invisible kernel and every
MF-visible consequence remain exactly computable from a single quotient.
