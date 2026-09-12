---
rg: 2
id: norm-corona-sparse-global-character-atom
kind: claim
title: A surviving elementary-abelian involution has a sparse global character atom in a norm corona
distinct_from:
  leavitt-character-mass-escapes-to-finer-characters: that concerns loss of positive normalized character mass and a missing common multiplicity reservoir; this selects a possibly rank-one global character projection, which survives in operator norm but need not carry positive trace.
  character-diracization-limit: that uses tensor powers to drive a tracial character toward a regular character; this selects one exact joint eigencorner by finite-window lifting and diagonalization, with no tensor powers.
artifacts:
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

Let `A` be a countable elementary abelian `2`-group and

```text
rho:A -> U(Q),
Q=(prod_n M_(d_n)(C))/(directSum_n M_(d_n)(C)),
```

be a homomorphism.  If `rho(a_0)!=1`, then there are a nonzero projection
`P in Q` and a character `chi:A->{+1,-1}` such that

```text
rho(a)P=chi(a)P                    for every a in A,       (SGA1)
chi(a_0)=-1.                                               (SGA2)
```

The projection may have vanishing normalized rank and can be rank one on
its nonzero coordinates.  Consequently diffuse normalized character mass
does not imply absence of operator-norm character atoms.

This does not by itself close the Leavitt argument.  Branch and transverse
shear may place two orthogonal copies equivalent to `P` inside a larger
returned character sector without making `P` equivalent to two subprojections
of itself.  Stable finiteness forbids the latter, not the former.  The missing
condition remains a return to the same finite multiplicity reservoir.

