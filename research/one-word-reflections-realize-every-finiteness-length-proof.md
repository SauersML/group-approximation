---
rg: 2
id: one-word-reflections-realize-every-finiteness-length-proof
kind: route
title: Lift a Stallings-Bieri subdirect product through its coordinate orbits
target: one-word-reflections-realize-every-finiteness-length
requires:
  - finite-orbit-subgroups-inherit-internal-mf-reflections
  - perfect-mf-reflection-over-residually-p-actor
---

Let

```text
R_n=F_2^n
```

and let `chi_n:R_n->Z` send each standard free generator in every factor to
`1`.  Put

```text
S_n=ker(chi_n).
```

The classical Stallings--Bieri theorem says that `S_n` is of type `F_(n-1)`
but not `FP_n`; the failure is witnessed by non-finite generation of the
relevant integral homology module.  In particular it is not of type `F_n`
(see also Mihalik, `Stallings' Group is Simply Connected at Infinity`,
arXiv:2506.19195, for the homotopical formulation).  The projection of `S_n`
onto every `F_2` factor is onto: prescribe an element in one factor and cancel
its `chi_n`-value with a power of a generator in a different factor.

Set

```text
T_n=S_n.                                                 (FLP1)
```

The product `R_n` is torsion-free, residually `2`, and linear in
characteristic zero, and all three properties pass to subgroups.  Hence
`T_n` has these properties without any finite extension.

Take the product of `n` internal free reflections, with visible quotient
`R_n`, and let `K_n` be the preimage of `T_n`.  The finite-orbit subgroup theorem gives
all target-factorization, closure, residual, and completion formulas.  It
also gives finite generation because `T_n` is finitely generated and its
projection onto each free factor is surjective.

The common residual contains the nonidentity seed involution.  Consequently
`K_n` is neither residually finite nor maximally almost periodic and admits
no faithful finite-dimensional linear representation over any field.  The
target-factorization bijections preserve both dimension and field, however,
so its full finite-dimensional representation theory is exactly the pullback
of that of the characteristic-zero linear group `T_n`.

The actor `T_n` moves the identity coordinate through every coordinate inside
each of the `n` base families.  The diagonal product of one seed involution
from each family normally generates the entire base by the coordinate
isolation argument in the finite-orbit theorem, proving `(FL2)` without
altering the visible quotient.  The base is perfect, so
`perfect-mf-reflection-over-residually-p-actor` with `p=2` gives the
finite-`2`, nilpotent, solvable, lower-central, and derived-series assertions.

An infinite virtually free group is of type `F_infinity`; thus `(FL3)` rules
out virtual freeness.  Muller--Schupp then rules out a context-free word
problem.  Finally, universal MF reflection is an isomorphism invariant, and
the distinct finiteness lengths of the `T_n` make the `K_n` pairwise
nonisomorphic.
