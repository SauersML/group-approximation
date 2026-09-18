---
rg: 2
id: no-group-carries-a-topological-bernoulli-absorption
kind: claim
title: No group has a full shift equivariantly homeomorphic to its product with a nontrivial subshift
distinct_from:
  gottschalk-surjunctivity-conjecture: that asks every strict pair to be impossible; this asks only that strict pairs whose decoder trivializes its fibres be impossible, a common weakening of Gottschalk, quantum surjunctivity and dual surjunctivity.
  full-shifts-with-different-alphabets-are-not-conjugate: that is the elementary fact that A^G and B^G with |A| != |B| are not conjugate, by counting constants; this forbids A^G = A^G x Y with Y a nontrivial subshift, where fixed-point counting only forces Y to have one fixed point.
  monomial-quantum-automata-are-topological-bernoulli-absorptions: that proves absorptions are strict monomial quantum automata; this is the conjecture that there are none.
  stable-finiteness-failure-is-algebraic-bernoulli-absorption: that identifies Kaplansky failures in characteristic p with algebraic absorptions; this forbids all topological absorptions, so it implies Kaplansky stable finiteness over every F_p.
---

**OPEN.** For every group `G`, every finite alphabet `A`, and every subshift `Y` with `|Y| >= 2` over a finite
alphabet, there is no shift-equivariant homeomorphism `A^G -> A^G x Y`.

**Implied by three open conjectures.**
- `gottschalk-surjunctivity-conjecture`, by (a) of `monomial-quantum-automata-are-topological-bernoulli-absorptions`.
  No route is recorded, to keep the graph acyclic, since this claim is a premise of the goal.
- `no-absorption-from-quantum-surjunctivity`: by (2) implies (1) of the monomial theorem.
- `no-absorption-from-dual-surjunctivity`: by `absorptions-give-post-surjective-strict-pairs` (ii).

**Implies.**
- **Kaplansky stable finiteness over every `F_p`.** If `M_n(F_p[G])` is not directly finite, then
  `stable-finiteness-failure-is-algebraic-bernoulli-absorption` gives a continuous equivariant isomorphism
  `(F_p^n)^G -> (F_p^n)^G x X_P` with `P` nonzero. `P` is finitely generated, so `X_P` is a closed invariant
  subgroup of some `(F_p^k)^G`, a subshift, and `|X_P| >= 2` by Pontryagin duality. This is an absorption.
- **With `strict-automata-yield-topological-bernoulli-absorptions`, the goal**
  (`gottschalk-via-no-topological-absorption`).

**Known cases.**
- Sofic groups, by Capobianco-Kari-Taati Theorem 2 and (ii) of the lemma, or by Gromov-Weiss and (a).
- **Reductions.** By (iv) of `absorptions-give-post-surjective-strict-pairs`, it suffices to treat finitely
  generated groups, and it holds for `G` iff it holds for every finitely generated subgroup. By (iii), an
  absorption over `G` has `Fix_N(Y) = {y_0}` for every normal `N` with `G/N` sofic.

**Why it is a useful target.** It sits below three open conjectures and above Kaplansky stable finiteness in
positive characteristic, and it is about a single homeomorphism rather than a pair of automata. A counterexample
must live on a nonsofic finitely generated group, and its `Y` must have `y_0` as its only point fixed by the
kernel of any sofic quotient.

## Attempts

- **2026-09-17 (swarm-0917-w6-w6-gs-last1, operator-algebras).** Obvious invariants and where they die.
  - **Fixed and periodic points.** Counting points fixed by `N` gives only `Fix_N(Y) = {y_0}` when `G/N` is
    sofic (lemma (iii)). On a group with no nontrivial sofic quotient, for instance an infinite simple nonsofic
    group, it forces nothing beyond `Fix_G(Y) = {y_0}`.
  - **Iteration.** Applying `Psi x id` repeatedly gives compatible homeomorphisms `A^G -> A^G x Y^n`. Their `Y`
    coordinates define an equivariant continuous surjection `A^G -> Y^N`: the image is closed and projects onto
    every `Y^n`. So a full shift factors onto a countable power of a nontrivial subshift. This is no
    contradiction on non-amenable groups. Sofic entropy can increase under factor maps: by Ornstein-Weiss, the
    2-symbol full shift over `F_2` factors onto the 4-symbol one. So the factor dies as an obstruction. Only the
    homeomorphism, not the factor, carries the information.
  - **Linear part.** Algebraic absorptions, with `X_P` as in `stable-finiteness-failure-is-algebraic-bernoulli-absorption`,
    are excluded exactly on groups where stable finiteness over `F_p` is known. No argument is recorded that
    excludes a nonlinear absorption on a group not already known to be surjunctive.
