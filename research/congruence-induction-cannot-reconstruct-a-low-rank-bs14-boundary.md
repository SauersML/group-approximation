---
rg: 2
id: congruence-induction-cannot-reconstruct-a-low-rank-bs14-boundary
kind: claim
title: Congruence induction has unbounded cost on a rank-one BS14 boundary
distinct_from:
  finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence: that classifies every exact endpoint by an odd congruence quotient; this proves that classification plus induction does not give quantitative boundary reconstruction.
  bs14-native-cells-cross-every-length-cutoff: that shows one exact atom crosses arbitrarily long packet cutoffs; this computes the index blowup incurred by reconstructing it from the BS subgroup instead of authenticating the atom.
  bs14-bounded-moments-cannot-extract-congruence-level: that excludes fixed scalar level fingerprints; this excludes the level-aware but representation-theoretically naive induction decoder.
---

Let `p` be an odd prime, put

```text
Q_p=PSL_2(F_p),
u=[[1,1],[0,1]],
h=diag(2,1/2),
H_p=<u,h><Q_p,
m_p=ord_p(4).                                          (CIB1)
```

Then

```text
H_p = F_p semidirect <4>,
|H_p|=p m_p,
[Q_p:H_p]=(p^2-1)/(2m_p)>=(p+1)/2.                    (CIB2)
```

Consequently, for every nonzero finite-dimensional `H_p`-representation
`sigma`, the canonical exact-extension operation

```text
sigma |-> Ind_(H_p)^(Q_p)(sigma)                       (CIB3)
```

has padding rank

```text
dim Ind(sigma)-dim(sigma)
 =([Q_p:H_p]-1)dim(sigma)>=(p-1)dim(sigma)/2.          (CIB4)
```

There is therefore no level-independent constant converting a low-rank
BS14 boundary into a global congruence atom by finite-group induction.

This obstruction is sharp on the canonical family. The compressed even-
Weil packets at growing primes delete one fixed line, have total cubic
Frobenius energy bounded below and above by absolute constants, and are
repaired by restoring exactly that one line. Replacing this native one-line
completion by `(CIB3)` would add at least `(p-1)/2` dimensions. Thus the
exact odd-congruence classification identifies where the missing atom
lives, but does not recover it with the energy-linear bound `(FBR2)`.

Any successful reverse low-rank theorem must authenticate the ambient
irreducible congruence atom (or an equally efficient cross-packet cell) from
the two residuals. It cannot first isolate an arbitrary BS boundary type and
then induce it to the classified finite quotient.

This does not refute `(FBR2)`: the Weil family itself has the efficient
native completion. It refutes only the general induction-based use of the
new exact classification.
