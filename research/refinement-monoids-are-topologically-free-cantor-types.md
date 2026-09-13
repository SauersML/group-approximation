---
rg: 2
id: refinement-monoids-are-topologically-free-cantor-types
kind: claim
title: Every countable simple conical refinement monoid other than 0 and Z^+, pointed at a nonzero element, is the clopen type semigroup of a minimal topologically free action of a free group on the Cantor space
distinct_from:
  simple-refinement-monoids-are-minimal-cantor-types: that realizes the monoid by some minimal action with no control of fixed points; this realizes it by a topologically free action of a free group, generic among Wehrung's witness tuples.
---

**Theorem.**  Let `M` be a countable simple conical refinement monoid with
`M != {0}` and `M` not isomorphic to `Z^+`, and let `e in M` be nonzero.  There
is an action of the free group `F_infinity` of countably infinite rank on the
Cantor space `X` with the following properties:
* it is minimal;
* it is topologically free: every nontrivial element fixes no nonempty open
  set pointwise;
* `(S(X, F_infinity), [1_X]) ≅ (M, e)`.

Its invariant Borel probability measures are the states of `M` normalized at
`e`.  In Wehrung's setting such actions are generic.  Tuples of measure-preserving
automorphisms, one witness for each piece of a fixed exhaustive decomposition
of the equal-measure pairs, form a Polish space, and a comeager set of tuples
generates a free group acting topologically freely.

**Consequences.**
* Topologically free, minimal, measure-free Cantor actions can have `[1_X]`
  finite and `2[1_X]` properly infinite
  (`topologically-free-minimal-cantor-action-with-finite-clopen-type`).
* Their type semigroups are not almost unperforated: `3(2u) <= 2u <= 2u`
  holds while `2u <= u` fails.  As Boldrini--Prasad's examples already show
  (they do not cite Rainone), this answers Rainone's first page-33 question
  (arXiv:1502.06153): minimal properly outer actions satisfying the
  hypotheses of his Theorem 4.22 whose type semigroup is not almost
  unperforated (`rainone-non-almost-unperforated-minimal-outer-action-exists`).
  His particular question, for free actions of `F_2`, stays open
  (`free-minimal-cantor-action-with-finite-clopen-type`).
* For such an action, `A = C(X) rtimes_r F_infinity` has the following
  properties.
  * It is simple, since the action is minimal and topologically free
    (Archbold--Spielberg; recalled, not re-verified).
  * It is exact and traceless: a trace would restrict to an invariant measure.
  * `1_X direct_sum 1_X` is properly infinite.
  * In Rainone's Theorem 4.21, condition (5) holds and condition (1) fails.
    So the monoid-level implication "no state => purely infinite" fails for
    minimal properly outer actions on `C(X)`.
* Whether `A` is purely infinite is open.  By Rainone's Theorem 4.16 this is
  whether `1_X` is properly infinite in `A`
  (`cantor-crossed-product-with-finite-type-is-mixed`).  If it is not, then `A`
  is neither stably finite nor purely infinite.

**Priority.**  The method and the main application are due to P. Boldrini
and A. Prasad (arXiv:2607.01896v1, 2 Jul 2026).
* Their Theorem 6.10: for a countable 2-divisible simple refinement cone that
  is not almost unperforated, a generic countable subgroup of `Aut(B, mu)` (a
  Fraïssé-limit measure) is dense, isomorphic to `F_infinity`, and acts
  topologically freely.
* Their Theorem 6.1 gives minimality, and Corollary 6.12 the measure-free
  case.
* The statement here drops 2-divisibility and non-almost-unperforation, and
  allows any nonzero `e`.  Its proof uses exhaustive witness cosets and
  point steering, instead of density and induction on word length.  It was
  found independently and later, and claims no novelty of method.

Status: proved in the route below, unreviewed.
