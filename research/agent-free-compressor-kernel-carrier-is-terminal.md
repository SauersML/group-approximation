---
rg: 2
id: agent-free-compressor-kernel-carrier-is-terminal
kind: route
title: Rule out canonical microstates by averaging distinct quotient-kernel elements
target: non-hyperlinear-group
requires:
  - finite-inclusion-is-free-self-compressor-quotient
  - agent-free-compressor-payload-kernel-fixed-sector
  - canonical-infinite-subgroup-has-zero-adjoint-fixed-density
---

Let `N=ker(theta)`.  It has finite index in the nonabelian finite-rank free
group `F`, hence is infinite.  If a canonical microstate sequence existed,
the robust shared-BCS gap and marked-carrier separation would make `(PKF1)`
give

```text
liminf tr_ad(E_n)>0.                                   (KCT1)
```

For a fixed `n in N`, choose once and for all an expression of `n` as a
product of conjugates of the finite normal generators.  Telescoping, using
`(PKF2)` and `(PKF3)`, gives

```text
||(S_n(n)-1)E_n||_2->0.                               (KCT2)
```

Thus `(KCT2)` holds for every fixed element of the infinite subgroup `N`.
The canonical infinite-subgroup theorem forces `tr_ad(E_n)->0`, contradicting
`(KCT1)`.  The exact perfect tracial representation in the compiler proves
that the marked word is nontrivial, so the absence of canonical microstates
makes the resulting finitely presented group nonhyperlinear.

The finite child quotient, predicate Reynolds rank jump, and tracial
self-copy equality are therefore unnecessary after `(PKF1)--(PKF3)`.  They
remain possible ways to construct the sector, but are not part of the
terminal implication.

