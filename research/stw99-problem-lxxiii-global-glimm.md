---
rg: 2
id: stw99-problem-lxxiii-global-glimm
kind: claim
title: Full square-zero elements exist at every scale without finite-dimensional representations (STW Problem LXXIII, the Global Glimm Problem)
root: true
distinct_from:
  stw99-problem-lxv-jiang-su-embeddings: that asks for unital Jiang-Su embeddings; this nilpotent-supply problem is its identified load-bearing half via dimension-drop semiprojectivity.
  stw99-problem-lxxii-weakly-purely-infinite: that asks whether weak and strong pure infiniteness coincide; by Kirchberg-Rordam 4.15 plus Thiel-Vilalta 7.1 the two problems share the ideal-filtration and property (V) mechanisms recorded in the LXXII recon.
artifacts:
  - research/artifacts/stw99-structural-cu-cluster-2026-08-30.md
  - research/artifacts/stw99-lxxii-weakly-pi-recon-2026-08-30.md
---

**Problem LXXIII of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(the Global Glimm Problem).  If `A` has no nonzero finite-dimensional
representations, must there be, for each `a ∈ A₊` and `ε > 0`, a
square-zero `x` whose generated ideal contains `(a − ε)₊`?  (Unital
form: a FULL square-zero element.)

Known: Thiel--Vilalta Thm 7.1 — the Global Glimm Property ⟺ nowhere
scattered + ideal-filtered `Cu` + property (V); nowhere scatteredness
is equivalent to the hypothesis; so the problem IS "no
finite-dimensional representations ⟹ ideal-filtered + (V)".

Known-positive corners (TV's Global Glimm introduction, Thm 5.8, Rem
5.7, Cor 5.3): topological dimension zero and stable rank one both give
ideal-filteredness AND property (V) (the latter via residual stable
finiteness); sup-semilattice-ordered `Cu` gives (V) outright; and for
separable `A` of finite nuclear dimension, the central sequence algebra
`F(A)` has the Global Glimm Property IFF `A` is `Z`-stable — wiring
this problem into the XXXVIII/XXXIX central-sequence circle.

## Attempts

* This lane's LXXII recon (artifact above) already dissected the two
  Thiel--Vilalta conditions in the weakly-purely-infinite instance:
  property (V) verified there except the join-fitting defect
  `d'_2 ≤ ∞d''_1`, and ideal-filtration reduced to one hereditary
  positioning statement with both subequivalences free.  The Global
  Glimm problem is the SAME two gaps without the wpi crutch (no
  `∞`-absorption to close joins), so the recon's obstruction analysis
  transfers verbatim: the join-fitting defect is the whole problem in
  the two-generator case, and any counterexample must realize a `Cu`
  where two full elements have no full common square-zero refinement
  — a refinement-monoid gadget with no known C*-realization (same
  wall as LX's non-separative target).  Recorded: LXXIII counter-
  examples and LX counterexamples both need the refinement-monoid
  realization breakthrough; a realization method would likely settle
  both negatively at once, while structural progress on join-fitting
  settles LXXIII's two-generator case positively.
