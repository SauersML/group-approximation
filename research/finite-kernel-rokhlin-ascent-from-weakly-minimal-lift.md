---
rg: 2
id: finite-kernel-rokhlin-ascent-from-weakly-minimal-lift
kind: claim
title: If a finite-entropy action of a Rokhlin-maximal quotient lifts across the finite kernel and is weakly contained in all free actions, the extension is Rokhlin-maximal
distinct_from:
  rokhlin-maximality-ascends-co-amenable-subgroups: that ascends from a co-amenable subgroup through Følner windows; this ascends across a finite kernel through one liftable action of the quotient, with no subgroup of W isomorphic to the quotient.
  rokhlin-finite-kernel-ascent-iff-liftable-entropy-unbounded: that characterizes maximality of the extension; this gives sufficient conditions, of which weak containment and Bernoulli lifting are the checkable ones.
artifacts:
  - research/artifacts/rokhlin-finite-kernel-ascent-equivalence-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by [[finite-kernel-rokhlin-ascent-weakly-minimal-lift-proof]].

Let `N ◁ W` be finite and `Q = W/N` finitely generated and Rokhlin-maximal at every `q`. Suppose some free ergodic
`Q`-action `Y_0` with `h^Rok_Q(Y_0) < ∞` lifts, meaning `Y_0 ≅ X_0/N` for a free `W`-action `X_0`, and that for a
constant `c`

    h_Q(Y_0 × L^Q | B(Y_0)) >= H(L) - c    for uniform bases L of arbitrarily large entropy.

Then `W` is Rokhlin-maximal at every `q`. The displayed condition holds with `c = 0` in each of these cases:
- (i) `Y_0` is weakly contained in every free p.m.p. `Q`-action;
- (ii) some Bernoulli shift of `Q` with finite-entropy base lifts to a free `W`-action;
- (iii) `seward-direct-product-relative-rokhlin-entropy-conjecture` holds over `Q`, with `Y_0 = Ω/N`, the twisted
  section action of `rokhlin-finite-kernel-ascent-iff-liftable-entropy-unbounded`.

**Why only these.** Weak containment is the only lower-bound transfer without finite models in the sources read.
For `Ω/N` it asks for an approximate trivialization of the extension class on Bernoulli orbit relations of `Q`.
Artifact Section 5 is a mechanism analysis of why rigid extensions of Gohla–Thom type resist this.

Section 3 of the artifact.
