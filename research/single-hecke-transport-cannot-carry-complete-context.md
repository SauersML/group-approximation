---
rg: 2
id: single-hecke-transport-cannot-carry-complete-context
kind: claim
title: One nonreducing Hecke transport cannot carry a complete corner PVM, and the minimal finite-anchor filter has a finite absorber
artifacts:
  - research/single-hecke-transport-rank-balance-proof.md
distinct_from:
  extraspecial-fusion-filter-local-normalizer-globalization: that identifies nonnormal Hecke transport as the remaining class; this computes the class with one stable letter and proves its unital-context obstruction.
  five-clifford-diagonal-spin-absorbs-the-full-orbit-lock: that gives a finite normalizer model retaining off-character leakage; this treats a genuinely nonnormal finite anchor and its off-corner rank balance.
  strict-compressor-mixed-return-collapses-shared-pauli-sign: that uses equality of unitarily conjugate finite-dimensional subgroup algebras to control one mixed return; this is a projection-level compression theorem with an explicit D8-in-S4 absorber.
---

Let Q be a projection and U a unitary in any finite tracial von Neumann
algebra.  If P_1,...,P_m are orthogonal projections summing to Q, then
the compressed transported effects
```text
R_v=Q U P_v U^* Q
```
satisfy
```text
sum_v R_v=Q U Q U^*Q,
Q-sum_v R_v=Q U(1-Q)U^*Q.                              (SHT1)
```
In particular
```text
sum_v R_v=Q       if and only if       UQU^*=Q.           (SHT2)
```
Thus one genuinely nonreducing Hecke move cannot transport a complete
PVM into the same corner.  Its missing mass is exactly
```text
tau(Q)-tau(Q U Q U^*Q)
 =||(1-Q)U^*Q||_2^2
 =||Q U(1-Q)||_2^2.                                     (SHT3)
```
For two compressed words the multiplication defect is likewise exact:
```text
(QGQ)(QHQ)-QGHQ=-QG(1-Q)HQ.                              (SHT4)
```

The smallest extraspecial example already has a finite absorber.  Inside
S_4 take
```text
E=<r=(1 2 3 4),s=(1 3)> isomorphic to D_8,
J=r^2=(1 3)(2 4),        a=rs=(1 4)(2 3),
t=(3 4).
```
Then t a t^-1=J and t J t^-1=a.  With
```text
q=(1-J)/2,
p_epsilon=q(1+epsilon a)/2,       epsilon in {+1,-1},
```
one has the exact Hecke filter
```text
q t p_+ t^-1 q=0,
q t p_- t^-1 q=p_-,
q t q t^-1 q=p_-.                                      (SHT5)
```
The canonical traces are
```text
tau(q)=1/2,             tau(p_+)=tau(p_-)=1/4.           (SHT6)
```
Hence one losing-pair zero is obtained, but exactly half the spin corner
is lost; adding the missing p_+ is a finite completion.  The left regular
representation of S_4 realizes every relation and trace in (SHT5)--(SHT6)
in dimension 24.

The universal group with only this routing relation,
```text
<E,t | t a t^-1=J>,
```
is an HNN extension of a finite group along order-two subgroups.  It is
virtually free and residually finite.  Every finite packet of its
canonical trace, including all fixed q,t,p_epsilon corner moments and
leakage norms, is matched exactly by a finite quotient regular
representation.

The same conclusion holds for any finite graph-of-finite-groups Hecke
router: its full group C*-algebra is residually finite-dimensional.
Therefore no source-visible algebraic element can vanish in all of its
finite-dimensional representations yet survive in an infinite tracial
completion.

A successful nonnormal fusion compiler must consequently go beyond a
single compressed context and beyond finite-subgroup HNN routing.  It
must use an infinite host relation that quantitatively controls
off-corner leakage while preserving a positive pointed corner.  Finite
fusion identities alone cannot do this.
