---
rg: 2
id: simple-group-relator-width-in-finite-simple-targets
kind: claim
title: A finitely presented simple nonsofic group has uniformly bounded relator width in every symmetric, alternating, sporadic and bounded-rank Lie type group
distinct_from:
  simple-group-support-and-semisimple-rank-models-collapse: that collapses weak models with support or semisimple rank lengths on any finite group; this proves the Glebsky--Rivera width bound itself, for every bi-invariant length, on the symmetric, alternating, sporadic and bounded-rank Lie type groups.
  glebsky-rivera-w-sofic-criterion: that says non-weak-soficity is a uniform width bound over all finite groups; this proves that bound over a large class of finite groups for every finitely presented simple nonsofic group.
  literal-mark-conjugacy-width-unbounded: that shows the non-MF group E has unbounded relator width, because E is sofic; this is the opposite conclusion for simple nonsofic groups, restricted to simple and symmetric targets.
  howie-pro-p-tuple-fails-the-profinite-certificate-at-a5: that kills one proposed certificate tuple at a single finite quotient; this proves bounded width for explicit groups over whole families of finite groups.
---

**ESTABLISHED.** Let `G = <X | R>` be an infinite finitely presented simple group. For a
finite group `Q` and `a in Q^X`, let `w_Q(a)` be the least `K` such that every generator
`a_x` is a product of at most `K` `Q`-conjugates of relator values `r(a)^(+-1)`.
`w_Q(a)` is finite, because `G` has no nontrivial finite quotient.

- **(A) Bounded rank.** For every `rho` there is `K_rho(G)` with `w_Q(a) <= K_rho` for
  every finite simple group `Q` of Lie type of rank at most `rho`, every sporadic group
  `Q`, and every `a`. No soficity hypothesis is needed.
- **(B) Symmetric and alternating.** `G` is not sofic iff there is `K(G)` with
  `w_Q(a) <= K` for all `Q = Sym(n)`, all `Q = Alt(n)` and all `a`.
- **(C) Weak models.** If `G` is not sofic, then no sequence of weak models of `G`
  into (finite groups with bi-invariant lengths) can have all targets symmetric,
  alternating, sporadic, or of Lie type of bounded rank. The lengths are arbitrary.
  For any bi-invariant `l`, `l(a_x) <= K max_r l(r(a))`.

**Consequence for the binary Leavitt unit group.** `R^x = L_(F_2)(1,2)^x` is finitely
presented, simple and nonsofic. So every weak model sequence of `R^x` must eventually use
finite groups that are neither simple nor symmetric, or classical groups of unbounded
rank. There its relator width is unconstrained by anything on record. The same
dichotomy holds for Khanh's group, which is `R^x`, and for every finitely presented simple
nonsofic group. For Thompson's group `V`, (A) holds and (B) is equivalent to
`thompson-v-not-sofic`.

**Why it is the certificate, partially.** By `glebsky-rivera-w-sofic-criterion`, `R^x` is
not weakly sofic iff the bound of (B) holds over **all** finite groups. This theorem proves
it over the finite simple groups except classical groups of unbounded rank, and over the
symmetric groups. The remaining classes are:
- classical groups of unbounded rank over `F_q`. If `G` is not `F_q`-linear sofic, the
  rank collapse (item 3 of `simple-group-support-and-semisimple-rank-models-collapse`,
  any characteristic) gives some relator value with rank at least `delta_0` times the
  largest generator rank. Bounded width would then follow from a covering lemma that is
  **not** established here: products of boundedly many conjugates of an element at rank
  distance `rho` from the center cover every element of rank `<= C rho`, uniformly in the
  classical group. The needed input is a centralizer bound
  `|C_Q(g)| <= q^(O(1)) q^(dim Q - 2 rho (d - rho))`.
- non-simple finite groups with thin conjugacy classes, such as wreath products with small
  coordinate-permuting groups. This is where Glebsky's permanence room lives.

Derivation: `simple-group-relator-width-in-finite-simple-targets-proof`. Unreviewed.
