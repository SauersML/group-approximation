---
title: STW LXXXIV checkpoint --- almost-free permutation wreath products (2026-08-30)
---

## Result

Let a countable abelian group `A` of finite rational rank `r` act on a
countable set `S` with finite point stabilizers, and let `L` be any countable
locally finite group.  Then, for `r>=1`,

`dim_nuc C*((direct_sum_S L) rtimes A) <= (r+1)9^r-1`.

For rank zero the group is locally finite and the exact dimension is zero.
The stabilizer orders and the finite-subgroup complexity of `L` may both be
unbounded.

## New finite-stage observation

Eckhardt--Wu Theorem 5.14 treats the regular Bernoulli index set.  Their
proof extends, with one necessary scalar-fiber correction, to every
permutation index set with finite stabilizers for the abelian actors needed
here.  For a finitely generated abelian actor `V` of rank `q`, choose a
torsion-free finite-index subgroup `K`.  Finite stabilizers imply
that `K` acts freely on the index set.  At a central-spectrum fiber fixed by
`N<=V`, the group `K intersection N` is still free on the indices.  Choosing
orbit representatives regroups the fiber as

`B^(tensor (K intersection N))`,

where `B` is scalar, a matrix algebra, or a UHF algebra.  For `B!=C`, this
is precisely the strongly outer Bernoulli model used in Eckhardt--Wu Example
4.9; the remaining finite quotient is handled as in their Theorem 5.14 and
has nuclear dimension at most one.  For `B=C`, however, the fiber crossed
product is `C*(N)` for a subgroup `N<=V`, and has nuclear dimension
`rank(N)<=q`.  Thus the stabilizer-fiber parameter is `max{1,q}`, not one.
Eckhardt--Wu Theorem 5.1 and `(5.1)` give

`dim_nuc+1 <= 9^q(max{1,q}+1)`,

and hence `(q+1)9^q-1` for positive rank.

The source was checked directly at arXiv:2408.07223: equation (5.1), Theorem
5.1, Example 4.9, Lemma 5.13, and Theorem 5.14.

## Countable exhaustion and strictness

Simultaneously exhaust the locally finite lamp by finite subgroups, the
actor by finitely generated subgroups, and the index set by the orbits of
finitely many sites.  Every stage is covered by the generalized finite-stage
estimate, and the bound depends only on rational rank.  The group-algebra
inductive limit preserves the uniform bound.

This is strictly broader than both earlier positive mechanisms as an action
criterion.  The action need not be regular.  For

`A=Z direct_sum direct_sum_(n>=1) Z/2`

acting on the disjoint union of `A/<e_n>`, the stabilizers are nontrivial and
vary through infinitely many torsion directions.  A single lamp together
with the infinite cyclic translation generates an infinite lamp subgroup,
so kernel-finiteness fails.  With lamp `Z/2`, the theorem nevertheless gives
the uniform bound `17`.

This does not settle arbitrary locally-finite-by-abelian groups: infinite
stabilizers destroy the free regrouping step and can leave non-Bernoulli
stabilizer fibers of uncontrolled nuclear dimension.
