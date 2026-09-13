---
rg: 2
id: finite-perfect-free-pairs-have-normal-rank-one
kind: claim
title: The free product of two nontrivial finite perfect groups has normal rank one
distinct_from:
  coprime-order-normal-generators-give-normal-rank-one: that is the general mechanism assuming normal generators of coprime orders; this supplies such generators for every pair of nontrivial finite perfect groups, using the odd order theorem.
  gordon-free-products-of-three-groups-have-normal-rank-above-one: that predicts normal rank above one for three or more nontrivial factors, finite perfect ones included; this shows two finite perfect factors never have it.
---

**ESTABLISHED** by `finite-perfect-free-pairs-normal-rank-one-proof` (direct proof
from standard finite group theory).

**Statement.** Let `A` be a nontrivial finite perfect group.
1. `A` has a normal generator whose order is a power of 2, and another whose order
   is odd. In particular `A` has normal rank 1, which is Wiegold's observation
   (Kourovka 5.52).
2. If `B` is also a nontrivial finite perfect group, then `A * B` has normal
   rank 1.

**Scope and trust.**
- The odd order theorem of Feit and Thompson is used, but not re-read.
- The rest is textbook material: Cauchy's theorem, the nilpotency of finite
  p-groups, and a standard lemma on normal subgroups of products of nonabelian
  simple groups, which is proved in the route.
- No novelty is claimed. Chen–Lodha note the special case of simple factors with
  torsion elements of coprime orders (arXiv:2510.26073, l.222).

**Why it matters.** Two factors are therefore never enough for Gordon's
conjecture when torsion is allowed. The open three-factor case, which already
includes three finite perfect groups, is
`gordon-free-products-of-three-groups-have-normal-rank-above-one`.
