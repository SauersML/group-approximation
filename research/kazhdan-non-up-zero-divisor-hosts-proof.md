---
rg: 2
id: kazhdan-non-up-zero-divisor-hosts-proof
kind: route
title: Property (T) rules out amenability, the Haagerup property, every stage of class C and maps onto Z; cyclic proper subgroups rule out residual finiteness
target: kazhdan-groups-without-unique-products-are-zero-divisor-hosts
requires:
  - arzhantseva-steenbock-kazhdan-groups-without-unique-products
---

Let `G` be infinite, torsion-free, Kazhdan, and without unique products. The
proof uses these standard facts:
- a Kazhdan group is finitely generated and has finite abelianization;
- property (T) passes to quotients and to finite-index subgroups.

**1. Not elementary amenable.** An amenable Kazhdan group is finite.
- Amenability gives almost invariant unit vectors in `l^2(G)`.
- Property (T) then gives a nonzero invariant vector.
- An invariant `l^2` function is constant and nonzero, which forces `G` to be
  finite.

Elementary amenable groups are amenable.

**2. Not inside a torsion-free virtually compact special group.** Suppose
`G <= G'`, where `G_0 <= G'` has finite index and is the fundamental group of
a compact special cube complex.
- By Haglund--Wise, *Special cube complexes*, GAFA 17 (2008), `G_0` embeds in
  a right-angled Artin group.
- That group acts properly on the universal cover of its Salvetti complex, a
  CAT(0) cube complex. So it has the Haagerup property, and so do its
  subgroups.
- `G ∩ G_0` has finite index in `G`, so it is infinite and Kazhdan.
- It is also a subgroup of `G_0`, hence Haagerup.

A group with both property (T) and the Haagerup property is finite, a
contradiction. This is the argument of `zero-divisor-host-not-special-proof`,
applied to a subgroup.

**3. Not in Linnell's class `C`.** Linnell (Forum Math. 5 (1993)) defines `C`
as the smallest class of groups that contains all free groups and is closed
under directed unions and under extensions with elementary amenable quotient.
Define stages by transfinite recursion:
- `C_0` is the class of free groups;
- `C_(a+1)` consists of the directed unions of groups in `C_a`, together with
  the groups that have a normal subgroup in `C_a` with elementary amenable
  quotient;
- at a limit ordinal `l`, `C_l` is the union of the `C_a` for `a < l`.

The stages increase, since the quotient may be trivial. Their union contains
the free groups and is closed under both operations: a directed union of
groups from stages `a_i` lies in stage `(sup a_i) + 1`. By induction every
stage lies in `C`, so the union equals `C`.

Suppose some infinite Kazhdan group lies in `C`, and let `X` be one at the least
possible stage `a`.
- **`a = 0`.** Impossible: a nontrivial free group maps onto `Z`, while `X`
  has finite abelianization.
- **`a` a limit.** Impossible: then `X` already lies in an earlier stage.
- **`a = b+1`, `X` a directed union of groups `X_i` in `C_b`.** `X` is
  finitely generated, so `X = X_i` for some `i`, contradicting minimality.
- **`a = b+1`, `N` normal in `X` with `N` in `C_b` and `X/N` elementary
  amenable.** `X/N` is Kazhdan and amenable, hence finite by step 1. So `N`
  has finite index in `X`, is infinite and Kazhdan, and lies in `C_b`,
  contradicting minimality.

So no infinite Kazhdan group lies in `C`.

**4. Not locally indicable.** `G` is a nontrivial finitely generated subgroup
of itself with finite abelianization, so it does not map onto `Z`.

**5. Cyclic proper subgroups rule out residual finiteness.** Suppose every
proper subgroup of `G` is cyclic and `G` is residually finite.
- Choose `g != 1` and a finite-index normal subgroup `K` not containing `g`.
- Then `K` is proper, hence cyclic, so `G` is virtually cyclic.
- So `G` is amenable, hence finite by step 1, a contradiction.

Finitely generated linear groups are residually finite (Mal'cev), and `G` is
finitely generated, so `G` is not linear. In `CS(u,d,p)`, the subgroups
`CS(v,d,p)` for `v >= u` are normal of finite index, since the quotient embeds
in `GL_d(Z/p^v)`, and they intersect in `I`. So every subgroup of `CS(u,d,p)`
is residually finite, and `G` is none of them.

**Existence.** `arzhantseva-steenbock-kazhdan-groups-without-unique-products`
supplies groups satisfying the hypothesis:
- the hyperbolic groups of its item 1;
- the subgroups `N` of its item 2;
- the Tarski monsters of its item 3.

That node records that all of them are infinite, torsion-free, Kazhdan, and
without unique products.

**Tarski monsters.** Let `M` be as in item 3, and put
`H = <supp alpha ∪ supp beta>`. Then `alpha beta = 0` already holds in `k[H]`
(`zero-divisor-support-subgroup-host-constraints`, item 1). If `H != M`, then
`H` is cyclic and torsion-free, so `k[H]` is `k` or `k[t, t^(-1)]`. Both are
domains, which is a contradiction.

QED
