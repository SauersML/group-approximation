---
rg: 2
id: rainone-free-f2-action-not-almost-unperforated
kind: claim
title: Some free minimal action of F_2 on the Cantor set has a type semigroup that is not almost unperforated (Rainone's particular page-33 question)
distinct_from:
  rainone-non-almost-unperforated-minimal-outer-action-exists: that is Rainone's general question, answered by topologically free actions of F_infinity (Boldrini-Prasad); this is his particular question, with a free action of F_2.
  free-minimal-cantor-action-with-finite-clopen-type: that asks for a free action of some countable group with no invariant measure and a finite clopen class; this asks only for failure of almost unperforation, for F_2, invariant measures allowed.
---

There is a free minimal action of `F_2` on the Cantor set `X` such that
`S(X, F_2)` is not almost unperforated.  By Ara--Bönicke--Bosa--Li,
Corollary B, this is the same as a free minimal action of `F_2` without
dynamical comparison.

Source: Rainone, arXiv:1502.06153, page 33, verbatim: "In particular, is there
a free and action of the free group F_2 on the Cantor set X for which
S(X, F_2, C) is not almost unperforated?"

A refutation would be as interesting: every free minimal action of `F_2` on
the Cantor set would have almost unperforated types.

## Attempts

* **What is known.**  Topologically free minimal actions of `F_infinity`
  without comparison exist, with or without invariant measures
  (Boldrini--Prasad, arXiv:2607.01896, Theorem 6.10 and Corollaries 6.11,
  6.12; independently `refinement-monoids-are-topologically-free-cantor-types`).
  Two gaps remain: rank 2, and freeness.
* **Firewall: amenable actions have comparison.**  Boldrini--Prasad (p. 9)
  list among the actions known to have comparison "Amenable minimal actions of
  groups with paradoxical towers --- a strong form of non-amenability
  satisfied by free groups, acylindrically hyperbolic groups and many natural
  classes of non-amenable groups --- on compact metrizable spaces", citing
  Gardella--Geffen--Kranz--Naryshkin (J. Reine Angew. Math. 797 (2023)).
  * So any example is a non-amenable action.  The GGKN statement itself has
    not been read here.
* **Rank 2 by Baire category on pairs: dense-generating pairs are not dense.**
  * In `Aut(B, mu)^2`, the pairs that both map a proper clopen `p` onto
    itself form a nonempty open set.  No pair in it generates a dense or
    `mu`-exhaustive subgroup, since no word moves a piece of `p` outside `p`.
  * So a Baire argument for `F_2` must run in a smaller closed subspace, for
    example with one generator `T` fixed and the other generic.
  * Where it dies: exhaustiveness then needs words in `T` and a generic `g`
    whose action on small pieces realizes prescribed measure-preserving
    matchings exactly, while finite data constrain `g` on atoms.  Nothing
    shown about `T` provides this.
* **Rank 2 by shift conjugation.**  `F_infinity` is the kernel of
  `F_2 -> Z`, with `Z` shifting generators.  An action of `F_infinity` with
  generators `g_n` extends to `F_2` iff `g_(n+1) = T g_n T^(-1)` for one
  homeomorphism `T`.
  * Generic tuples are not of this form.  One needs a pair `(T, g_0)` whose
    conjugates `T^n g_0 T^(-n)` generate an exhaustive group, which is the pair
    problem again.
* **Freeness by genericity (partial idea, unreviewed).**  For a word `w`, the
  tuples with `w(g)` fixed-point free form an open set.  A finite certificate
  suffices: a finite subalgebra whose atoms `d` satisfy `w(g)(d) ∧ d = 0`.
  * One letter, cancellative 2-divisible cone (the Bernoulli cone of BP
    Theorem 3.10): density holds.  Finite data send an atom `p` to
    `q = g(p)`.  Split `c = p ∧ q` into two halves of equal measure and swap
    them.  Map `p \ c` onto `q \ c`, which has the same measure by
    cancellation.  Homogeneity of the Fraïssé limit extends this.
  * Where it dies: for longer words the atom images along the word must be
    steered with every letter reused consistently, and this is not done.  For
    non-cancellative cones (the measure-free cone), `mu(p\c) + mu(c) =
    mu(q\c) + mu(c)` does not give `mu(p\c) = mu(q\c)`.
