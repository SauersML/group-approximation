---
rg: 2
id: agent-deligne-opnorm-minimum-block-escape
kind: claim
title: Nontrivial Deligne operator-norm sectors escape every minimum irreducible block cutoff
distinct_from:
  maslov-bounded-block-sector-gap: that gives a normalized-Hilbert--Schmidt energy lower bound proportional to the mass carried by bounded blocks; this operator-norm theorem excludes even one bounded irreducible block in every sufficiently accurate tuple.
  deligne-nontrivial-maslov-opnorm-sectors-are-empty: that excludes all point-norm matrix models and would compute the exact MF radical; this proves the strongest compactness consequence that follows from finite-dimensional invisibility alone and still allows tuples all of whose irreducible blocks diverge.
---

**ESTABLISHED.**  Fix a finite lifted presentation of Deligne's triple cover
`E_3`, substitute `z=omega I` for either nontrivial third root of unity, and
write `R` for the resulting finite list of twisted relators in the remaining
generators `S`.  For every `K>=1` there is `epsilon_K>0` such that the
following holds in every matrix dimension.

If a unitary tuple `U=(U_s)_(s in S)` has a nonzero common reducing block of
dimension at most `K`, then

```text
max_(r in R) ||r(U,omega I)-I||_op >= epsilon_K.          (OME1)
```

Consequently, if `U^(n)` is a point-norm asymptotic matrix model in a
nontrivial Maslov sector, then the minimum dimension of an irreducible block
of the finite-dimensional C-star algebra `C^*(U^(n))` tends to infinity.
Equivalently, for each fixed `K`, every sufficiently late coordinate has no
nonzero common invariant subspace of dimension at most `K`.

In particular, neither nontrivial twisted fibre admits a unital
star-homomorphism into a norm corona whose coordinate algebras are uniformly
subhomogeneous.  Any countermodel to
`deligne-nontrivial-maslov-opnorm-sectors-are-empty` must therefore be
operator-norm diffuse in the strong minimum-block sense: it is not enough for
bounded blocks merely to have asymptotically zero normalized rank.

DERIVATION
agent-deligne-opnorm-minimum-block-escape-proof

