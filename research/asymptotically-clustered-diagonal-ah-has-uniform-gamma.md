---
rg: 2
id: asymptotically-clustered-diagonal-ah-has-uniform-gamma
kind: claim
title: Asymptotically clustered diagonal AH systems have uniform property Gamma
distinct_from:
  point-dominated-diagonal-ah-has-uniform-gamma: that theorem discards a vanishing proportion of nonconstant coordinate maps and balances the remaining point evaluations; this theorem permits arbitrary, even full, coordinate weight when almost all eigenmaps form uniformly close packets.
  stw99-problem-xx-villadsen-algebras-uniform-gamma: that asks about the independently variable multiplicity-one coordinate maps in the positive-radius Villadsen regime; the packetability hypothesis below need not hold there.
artifacts:
  - research/artifacts/stw99-xx-clustered-eigenmap-gamma-2026-08-30.md
---

Let

```text
A = lim_n (C(X_n) tensor M_(r_n), phi_n)
```

be a unital simple diagonal AH algebra.  Write every later composite in
diagonal form

```text
phi_(n,m)(a)(y)
 = diag(a(lambda_1(y)),...,a(lambda_L(y))),
```

where `L=r_m/r_n`.  Suppose the following asymptotic packetability condition
holds.  For every stage `n`, finite subset `F` of the unit ball of its
building block, integer `k>=2`, and `epsilon>0`, there is a later stage `m`
such that the eigenmap indices decompose as

```text
{1,...,L} = R disjoint_union I_1 disjoint_union ... disjoint_union I_s,
```

with

```text
|I_t|=k,             |R|/L < epsilon,
max_(a in F) max_(i,j in I_t) sup_(y in X_m)
    ||a(lambda_i(y))-a(lambda_j(y))|| < epsilon
```

for every packet `I_t`.  Then `A` has uniform property Gamma.

The conclusion still holds when the composite coordinate weight is bounded
away from zero, or is identically one.  In particular, the hypothesis holds
if, from each fixed stage, the number `D_(n,m)` of distinct eigenmaps satisfies

```text
D_(n,m)/L_(n,m) -> 0
```

along a cofinal subsequence: group equal eigenmaps into `k`-packets and leave
at most `(k-1)D_(n,m)` indices ungrouped.

The witnessing projections generally have off-diagonal entries between the
blocks in a packet.  Thus the theorem does not put them in the canonical
Cartan and does not conflict with the Elliott--Niu relative-uniform-Gamma
obstruction.
