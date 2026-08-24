---
rg: 2
id: one-word-reflections-realize-every-finiteness-length-proof
kind: route
title: Symmetrize a Stallings-Bieri subdirect product and lift its finite coordinate orbits
target: one-word-reflections-realize-every-finiteness-length
requires:
  - finite-orbit-subgroups-inherit-internal-mf-reflections
  - finite-wreath-lift-of-internal-mf-reflection
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

The cyclic group `C_n` permutes the factors of `R_n`, preserves `chi_n`, and
therefore normalizes `S_n`.  Define

```text
T_n=S_n semidirectProduct C_n.                           (FLP1)
```

Finite-index invariance of `F_j` and `FP_j` shows that `T_n` is still of type
`F_(n-1)` but not `FP_n`.  It is residually finite because `S_n` is a subgroup
of the residually finite group `R_n` and `T_n` is a finite extension.
The product `R_n` is linear in characteristic zero, hence so is `S_n`.
Finite extensions of characteristic-zero linear groups are linear, for
example by inducing a faithful representation from the finite-index
subgroup, so `T_n` is linear in characteristic zero.

Take the product of `n` internal free reflections and adjoin the cyclic block
permutation.  This is the finite wreath lift with visible quotient

```text
R_n semidirectProduct C_n.
```

Let `K_n` be the preimage of `T_n`.  The finite-orbit subgroup theorem gives
all target-factorization, closure, residual, and completion formulas.  It
also gives finite generation because `T_n` is finitely generated and its
projection onto each free factor is surjective.

The common residual contains the nonidentity seed involution.  Consequently
`K_n` is neither residually finite nor maximally almost periodic and admits
no faithful finite-dimensional linear representation over any field.  The
target-factorization bijections preserve both dimension and field, however,
so its full finite-dimensional representation theory is exactly the pullback
of that of the characteristic-zero linear group `T_n`.

The actor `S_n` moves the identity coordinate through every coordinate inside
each of the `n` base families.  The cyclic actor `C_n` permutes those
families transitively.  Hence one seed involution normally generates the
entire base, proving `(FL2)`.

An infinite virtually free group is of type `F_infinity`; thus `(FL3)` rules
out virtual freeness.  Muller--Schupp then rules out a context-free word
problem.  Finally, universal MF reflection is an isomorphism invariant, and
the distinct finiteness lengths of the `T_n` make the `K_n` pairwise
nonisomorphic.
