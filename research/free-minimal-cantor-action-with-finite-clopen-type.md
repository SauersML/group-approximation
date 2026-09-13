---
rg: 2
id: free-minimal-cantor-action-with-finite-clopen-type
kind: claim
title: Some free minimal action of a countable group, ideally F_2, on a Cantor space has no invariant probability measure but a finite clopen type class
distinct_from:
  topologically-free-minimal-cantor-action-with-finite-clopen-type: that allows fixed points whose sets have empty interior and is established by generic witnesses in F_infinity; this demands a free action, the setting of Rainone's question, ideally of F_2.
---

There are a countable group `Gamma` and a *free* minimal action of `Gamma` on a
Cantor space `X` with the following properties.
* There is no invariant Borel probability measure.
* Some nonempty clopen `A` has a finite class `[1_A]` in `S(X, Gamma)`.

Strong form: `Gamma = F_2`.  A finite class in the measure-free case makes
`S(X, Gamma)` fail almost unperforation.  So the strong form answers Rainone's
question (arXiv:1502.06153, page 33) in the positive: whether a free minimal
action of `F_2` on the Cantor set can have a type semigroup that is not almost
unperforated.

**Why it matters.**  Free actions are the setting of dynamical comparison and
almost finiteness (Kerr), and of the paradoxical-tower theorem (GGKN).  The
known examples, `refinement-monoids-are-topologically-free-cantor-types`, are
topologically free, but freeness is not controlled.

## Attempts

* **Generic witnesses, freeness step.**  For a word `w`, the witness tuples
  for which `w(g)` has no fixed point are open: a finite clopen partition
  moved off itself certifies it.
  * Where it dies: density.  Lemma R of
    `refinement-monoids-are-topologically-free-cantor-types-proof` moves one
    point at a time, and removing every fixed point at once needs a global
    perturbation inside the atoms of a finite algebra.
  * Even for a single letter, if `g_k` maps an atom `p` onto itself, density
    needs a fixed-point-free measure-preserving automorphism of `B|p` with
    finitely many prescribed values.
  * Writing `mu(p) = 2y + 3z` (a swap and a 3-cycle) gives such an automorphism
    without the prescribed values.  Matching those values is unproved.
* **Finitely generated groups.**  `F_2` would need a generic 2-generation
  theorem: for a comeager set of pairs in `Aut(B, mu)`, the group they
  generate is `mu`-exhaustive.
  * Each exhaustiveness condition is open (some words realize the needed
    pieces).
  * Where it dies: density needs words whose action on small pieces realizes
    prescribed measure-preserving partial isomorphisms while respecting finite
    data on the two generators.
* **Freeing by profinite extensions (idea, unreviewed; moved from the
  topologically free claim).**  Take `X x lim F/N_k` with the diagonal action
  of a free group `F`.
  * The action is free.  Its clopen types are the direct limit of
    `S(X, N_k)`, and the whole space has class `[F:N_k][1_X]` at stage `k`.
  * Where it dies: the type semigroup of a finite-index subgroup must keep
    ever larger multiples of `[1_X]` finite.
  * A finite orbit shows the constraint is sharp: an orbit of size `d` forces
    `d[1_X]` to be finite.
* **Excluded classes.**
  * Free minimal amenable actions of groups with paradoxical towers
    (`stw99-xxxii-paradoxical-towers-citation`).
  * Groups with a normal infinite cyclic or locally finite subgroup acting
    minimally (`smoothing-normal-subgroup-cantor-dichotomy`).
