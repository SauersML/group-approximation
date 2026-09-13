---
rg: 2
id: wehrung-countable-refinement-monoids-group-measurable
kind: claim
title: Countable conical refinement monoids with order-unit are measured by groupoid-induced V-measures on countable unital Boolean rings, which are group-induced under a halving condition (Wehrung, LNM 2188)
distinct_from:
  opr-mixed-simple-refinement-monoid: that exhibits one abstract simple refinement monoid with a finite order unit whose double is properly infinite; this realizes countable refinement monoids as monoids of equidecomposability types of group actions on Boolean rings.
---

**Source.**  F. Wehrung, *Refinement monoids, equidecomposability types, and
Boolean inverse semigroups*, Lecture Notes in Math. 2188, Springer, 2017
(hal-01197354v3).

**Definitions (Wehrung).**
* A *V-measure* `mu: B -> M` on a Boolean ring `B` is additive on orthogonal
  pairs, has `mu^{-1}{0} = {0}`, and satisfies the V-condition: if
  `mu(c) = a + b` in `M`, then `c = a' direct_sum b'` in `B` with `mu(a') = a`
  and `mu(b') = b` (Definition 4.6.1).
* `mu` is *groupoid-induced* if `mu(a) = mu(b)` iff some measure-preserving
  partial isomorphism `f in Inv(B, mu)` sends `a` to `b`.  It is
  *group-induced* if `mu(a) = mu(b)` iff `a = direct_sum_i a_i` and
  `b = direct_sum_i f_i(a_i)` with finitely many `f_i in Aut(B, mu)`
  (Notation 4.7.4, Definition 4.7.7).
* An action of a group `G` on `B` by measure-preserving automorphisms is
  *`mu`-exhaustive* if every pair `a, b` with `mu(a) = mu(b)` has decompositions
  `a = direct_sum_i a_i`, `b = direct_sum_i g_i a_i` with `g_i in G`
  (Definition 4.7.12).
* `Z^+<B>//G` is the commutative monoid with generators `[a]_G` (`a in B`) and
  relations `[0]_G = 0`, `[g a]_G = [a]_G`, `[a direct_sum b]_G = [a]_G + [b]_G`
  (Section 1.2.1).

**Theorem (Wehrung).**  Let `(M, e)` be a countable conical refinement monoid
with order-unit `e`.

1. (Theorem 4.8.7 and its proof.)  There are a countable unital Boolean ring
   `B` and a groupoid-induced V-measure `mu: B -> M` with `mu(1) = e`.
2. (Proposition 4.7.10(1).)  If some `a in M` and `m >= 1` satisfy
   `2a <= e <= m a`, then every normalized groupoid-induced V-measure
   `mu: B -> (M, e)` on a unital Boolean ring is group-induced.
3. (Theorem 4.7.14(2).)  If `mu: B -> M` is a group-induced V-measure whose
   range generates `M`, then for every `mu`-exhaustive action of a group `G`
   on `B` the map `[a]_G -> mu(a)` is a monoid isomorphism
   `Z^+<B>//G -> M`.

**Limits of the theorem, from the same source.**
* Example 4.8.8: the monoid `P = <epsilon, 1 | epsilon + 1 = 1>` with order-unit
  `1` is groupoid-measurable but not group-measurable.  So a group
  realization of the pointed monoid `(M, e)` needs a condition such as the one
  in part 2.  `P` is not simple.
* Theorem 4.8.9: every countable conical refinement monoid, without a chosen
  order-unit, is group-measurable.
* Example 4.9.4: some countable conical refinement monoid with order-unit is
  not the type monoid of any *fundamental* Boolean inverse meet-semigroup.
  Such a monoid has no realization by an effective Hausdorff ample groupoid.
  The example is not simple.

**Use here.**  In a simple conical refinement monoid other than `0` and `Z^+`,
the halving condition of part 2 always holds, so parts 1--3 realize `(M, e)`
by a group action.  Stone duality turns this into a minimal Cantor action;
see `simple-refinement-monoids-are-minimal-cantor-types`.
