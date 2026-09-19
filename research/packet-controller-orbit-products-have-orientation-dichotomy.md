---
rg: 2
id: packet-controller-orbit-products-have-orientation-dichotomy
kind: claim
title: Packet-conjugate controller products are either gauge-blind or determinant-incompatible
distinct_from:
  normal-pauli-extensions-retain-the-orientation-character: that proves every normal two-qubit Pauli extension has an abstract C2 orientation character; this gives a direct matrix obstruction for the tempting finite product relation and also covers odd-prime Weyl packets.
  orientation-graded-mixed-returns-have-a-balanced-double: that twists an arbitrary graded extension by its two characters; this classifies one proposed grading-breaking row before any ambient extension is formed.
  finite-marked-involution-anchor-has-one-third-wrong-mass: that gives a Plancherel mass obstruction for an arbitrary finite anchor; this proves an exact all-or-nothing obstruction for products of conjugates of the native rank-one controller.
---

**ESTABLISHED.**  Let `ell` be prime.  Let `S(P)` be an irreducible Weyl
packet on `C^d`, where `d=ell^r`, and assume either `ell` is odd or
`ell=2,r>=2`.  Every packet word has determinant one:

```text
det S(g)=1,                         g in P.             (PCO1)
```

For odd `ell`, this follows because every coordinate shift is a disjoint
union of `ell^(r-1)` cycles of odd length and every coordinate clock has
determinant

```text
zeta^(ell^(r-1)(0+...+(ell-1)))=1.
```

For `ell=2,r>=2`, every coordinate shift and clock has equally many `+1`
and `-1` eigenvalues, hence determinant `(-1)^(2^(r-1))=1`; the central
sign also has determinant `(-1)^(2^r)=1`.

Let `P_0` be a rank-one projection and put

```text
C=1+(zeta-1)P_0,                  det(C)=zeta,          (PCO2)
```

where `zeta` is a primitive `ell`th root.  Thus for `ell=2`, `C=1-2P_0`
is exactly the fine controlled reflection.  In every extension sector in
which the packet covariance determines only the controller's outer action,
the controller has the standard multiplicity-gauge form

```text
S(g) tensor 1,                    t=C tensor V,
V^ell=1.                                                   (PCO3)
```

Consider the most direct proposed orientation pin: a product of packet
conjugates of powers of `t` is declared equal to a literal packet word,

```text
prod_(j=1)^n g_j t^(epsilon_j) g_j^(-1)=h,
g_j,h in P,                       epsilon_j in Z.       (PCO4)
```

Put `k=sum_j epsilon_j mod ell`.  Substitution of `(PCO3)` gives

```text
left side =
  (prod_j S(g_j)C^(epsilon_j)S(g_j)^*) tensor V^k.      (PCO5)
```

There are only two possibilities.

1. If `k=0`, the multiplicity factor in `(PCO5)` is the identity for every
   `V`.  The relation is exactly gauge-blind and cannot distinguish the
   literal orientation `V=1` from any other `ell`-torsion orientation.
2. If `k!=0`, the determinant of the label factor on the left of `(PCO4)`
   is `zeta^k`, whereas `(PCO1)` gives `det S(h)=1`.  Hence `(PCO4)` already
   fails in the intended pure label model `V=1`; it is incompatible with
   exact completeness rather than an orientation pin.

In particular, in the two-qubit controlled-reflection cell an even product
of packet conjugates cancels the involution `V`, while an odd product has
label determinant `-1` and cannot equal any Pauli word, all of which have
determinant `+1`.  The same dichotomy holds modulo `ell` in every odd-prime
Weyl packet.

This rules out a finite orbit-product repair of the typed fine selector,
including the tempting idea of multiplying an odd number of conjugate
rank-one controllers to obtain a literal packet anchor.  It does **not**
apply once a conjugator genuinely changes Leavitt scale and therefore does
not preserve the packet tensor decomposition `(PCO3)`.  The surviving mixed
row in `paired-same-reservoir-boundary-lemma` must be of exactly that
nonnormal, scale-changing kind (or use a finite-matrix-only coordinate
extraction); no product internal to the packet orbit can charge the
Schrodinger reservoir loss.
