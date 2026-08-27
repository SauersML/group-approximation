---
rg: 2
id: sl3-swap-fold-gap-forces-ambient-outlier
kind: claim
title: A swap fold gap quantitatively certifies an SL3 ambient-extension outlier
distinct_from:
  sl3-double-swap-involution-is-outlier-carried: that uses canonical regular moments and the large-prime depth-free sector theorem to prove separation from every exact lattice representation; this works at every prime and proves only the strictly sharper-looking but logically weaker separation from restrictions of exact same-dimensional ambient representations.
  sl3-amalgamated-free-enemies-are-ambient-extension-outliers: that inserts a Haar letter and its full amalgamated-free distribution into the unbalanced-torus inequality; this specializes directly to one self-adjoint involution and records an explicit finite-dimensional distance estimate using only one fold moment.
  unbalanced-torus-and-swap-commutation-do-not-control-fold-square: that exact countermodel proves the torus and separate rank-one relations do not force the fold square for an arbitrary actor packet; this theorem instead assumes proximity to an exact ambient actor and proves that a fold gap quantitatively forbids such proximity.
---

Fix a prime `p`, put

```text
C=SL_3(Z),       A=SL_3(Z[1/p]),
h=diag(p,1,p^(-1)),       C_+=C intersect h C h^(-1),
```

and fix the generating sets and word representatives used in
`unbalanced-torus-extracts-near-central-denominator-coordinate`.  For a
unitary lattice packet `X=(X_t)_(t in S)`, a unitary `H`, and a
self-adjoint involution `S_0`, write `X_c` for evaluation of the fixed word
representing `c in C`.  If `c in S_+`, put `c'=h^(-1)c h in C` and define

```text
b=sum_(t in S)||S_0 X_t-X_t S_0||_2^2,
r=sum_(c in S_+)||H X_(c') H^*-X_c||_2^2,
eta=||ev_(X,H)(R_tor)-1||_2,
d_A=inf_(sigma:A->U(d)) max_(t in S)||X_t-sigma(t)||_2. (SAG1)
```

The infimum is over exact ambient representations in the same dimension.
There is a constant `C_0<infinity`, depending only on the fixed words and
Kazhdan data, such that every such finite-dimensional packet satisfies

```text
1-|tr(H S_0 H^* S_0)|^2
  <= C_0 (b+r+eta^2+d_A^2).                            (SAG2)
```

Consequently, if the three displayed relation defects tend to zero while

```text
liminf (1-|tr(H S_0 H^* S_0)|^2)=epsilon>0,            (SAG3)
```

then

```text
liminf d_A >= sqrt(epsilon/C_0)>0.                     (SAG4)
```

In particular every hypothetical canonical microstate sequence for the
arithmetic double-swap group has a uniform ambient-extension outlier: its
swap commutators, overlap conjugacy defects, and torus-word defect vanish,
whereas the reduced fold word has trace zero.

This conclusion holds for every prime and uses only the single fold trace,
not the full amalgamated-free distribution.  It does **not** settle
`sl3-outliers-carry-no-balanced-free-involution`.  An exact representation
of the lattice need not extend in the same dimension to `A`; at large
primes the separate depth-free theorem is what upgrades the canonical
double-swap packet from ambient-extension outlier to lattice outlier.  The
remaining endpoint still has to exclude that lattice-outlier sector rather
than merely certify it.

DERIVATION
sl3-swap-ambient-outlier-gap-proof
