---
rg: 2
id: thompson-f-recurrent-f-sets-factor-through-the-abelianization
kind: claim
title: "Every transitive F-set with a recurrent Schreier graph factors through F/F′ ≅ Z²"
distinct_from:
  thompson-f-recurrent-orbits-have-stabilizers-containing-f: that proves recurrent stabilizers contain a copy of F; this asks for the much stronger containment of the commutator subgroup, i.e. that the action is abelian.
  f-functor-cocycles-need-an-exotic-recurrent-action: that proves the functor-cocycle method is circular unless an exotic recurrent F-set exists; this is the open question whether one exists.
  thompson-f-point-orbits-are-transient: that proves transience of the F-sets whose stabilizers fix an interior point; this concerns all F-sets.
---

**OPEN.** Let `H ≤ F` and let the Schreier graph of `F/H`, for a finite generating set, be
recurrent. Then `H ⊇ F′`. Equivalently, there is no *exotic recurrent `F`-set* in the
sense of `f-functor-cocycles-need-an-exotic-recurrent-action`.

**Why it matters.**
- *If true.* By item 2 of `f-functor-cocycles-need-an-exotic-recurrent-action`,
  every recurrent action of any group `G ⊇ F` has `F′` acting trivially. Then item 1
  there makes the method circular: a recurrent base, any functor `𝔉 : 𝐈 → 𝐀𝐦𝐞𝐧`, and a
  cocycle with amenable kernel can prove amenability of `G` only if amenability of `F` is
  already an input. Together with the stabilizer kill
  `thompson-f-recurrent-orbits-have-stabilizers-containing-f`, recurrence would then be
  useless for the flagship `thompson-f-is-amenable` in every known form.
- *If false.* An exotic recurrent `F`-set is extensively amenable and is a faithful-type
  action with non-abelian image. It is the only remaining base on which a
  Juschenko–Monod-style cocycle for `F` could run with recurrence as its engine.

**Known constraints on a counterexample `F/H`.** Every conjugate of `H`:
- contains a copy of `F`;
- meets every `Z³ ≤ F`;
- meets every rigid copy `F_p` in a subgroup with no fixed point in `int [p]`, so in
  particular `H` has the single orbital `(0,1)`;
- contains no end-rigid subgroup `F_[0,c]` or `F_[c,1]`.

Also, `H` is not normal: every nontrivial normal subgroup of `F` contains `F′`
(Cannon–Floyd–Parry, as used in `thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived`). And `F/H` is an amenable Schreier graph, so `H` is co-amenable in
`F`.

## Attempts

- **2026-09-17 (swarm-0917-w4-f-extensive).** Derived the four constraints above; see
  `f-functor-cocycles-need-an-exotic-recurrent-action` items 3–4.
  - *Tried and discarded as candidates:* stabilizers of points, finite sets and germs at
    interior points (transient by `thompson-f-point-orbits-are-transient`), and coset
    spaces of end-rigid subgroups (they collapse to `Z²`-sets).
  - *Not yet examined:* setwise stabilizers of infinite sets with one orbital, such as the
    parity-of-depth subsets of `D`, and centralizers of fixed-point-free
    homeomorphisms. Heuristically these have large Schreier graphs containing planted
    copies of the dyadic graph, as in Step 2 of `thompson-f-point-orbits-are-transient-proof`,
    but no rough embedding has been produced.
  - *Where the natural proof stalls:* a rough embedding of a transient graph into `F/H`
    needs some point of `(0,1)` whose `H`-orbit data is finite. The constraints say `H`
    moves every interior point, and a general transfer is missing.
