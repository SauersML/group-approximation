---
rg: 2
id: atomic-irs-strict-designs-are-nonsurjunctive-quotients
kind: claim
title: An atomic invariant random subgroup carries a strict automaton design exactly when its normalizer quotient is not surjunctive
distinct_from:
  atomic-noncohyperlinear-irs-forces-nonhyperlinear: that extracts a non-Connes-embeddable quotient factor from an atomic IRS character by finite-index induction; this is the cellular-automaton version, an exact equivalence between strict shape-dependent designs on the Schreier graph and non-surjunctivity of the normalizer quotient.
  injective-automata-restrict-to-schreier-graph-automata: that pushes an automaton over a group down to the coset space of a subgroup of that group; this starts from rules defined on Schreier graphs of a free group and lifts them to automata over the normalizer quotient, and back.
  surjunctivity-passes-to-subgroups: that is heredity under subgroups; this identifies which invariant random subgroups carry strict designs, and uses heredity only to reduce to finitely generated groups.
artifacts:
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
---

**ESTABLISHED** by `atomic-irs-strict-designs-are-nonsurjunctive-quotients-proof`.

Let `Gamma = F_r`, and let `mu` be an ergodic invariant random subgroup of `Gamma` with an atom `H`.
Then `mu` is uniform on the finite conjugacy class of `H`, `N_Gamma(H)` has finite index, and
`Q = N_Gamma(H)/H` is finitely generated.

A **design** is a pair of shape-dependent automata `(tau, sigma)` on Schreier graphs of `Gamma`.
Each is given by a local rule on finite coloured rooted labelled balls. The IRS `mu` **carries** the
design if the root is a.s. forward-good (`sigma tau x = x` at the root for every colouring) and
reverse-bad (`tau sigma y != y` at the root for some colouring) with positive probability.
Equivalently, over a.e. Schreier graph `tau` has the local left inverse `sigma`, and with positive
probability `tau` is not surjective. Artifact Section 2, Lemma 2.1.

**Theorem.** `mu` carries a strict design iff `Q` is not surjunctive.

- For normal `H`, this says `delta_H` carries a strict design iff `F_r/H` is not surjunctive.
- **Corollary.** Gottschalk's conjecture is equivalent to: for every `r`, no atomic ergodic IRS of
  `F_r` carries a strict design. Every non-surjunctive group has a finitely generated non-surjunctive
  subgroup (artifact Lemma 2.3).

**Proof shape.**
- (=>) `Q` acts freely on `H\Gamma` by label-preserving automorphisms with finitely many orbits.
  Shape-dependent rules commute with it, so the design is an injective, non-surjective automaton over
  `Q` with alphabet `A^k`.
- (<=) A strict pair over `Q` is read on each orbit layer through the conjugated lifted memory words
  `g_i^-1 m_s g_i`. The layer is visible in a bounded ball, because distinct conjugates of `H` are
  separated by finitely many words.

Full proof: artifact Section 3.
