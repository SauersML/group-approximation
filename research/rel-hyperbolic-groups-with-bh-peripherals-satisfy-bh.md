---
rg: 2
id: rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh
kind: claim
title: A finitely generated relatively hyperbolic group with solvable word problem whose peripheral subgroups embed in finitely presented simple groups embeds in a finitely presented simple group
distinct_from:
  hyperbolic-groups-satisfy-boone-higman: that is the case with no (or hyperbolic) peripheral subgroups, proved by Belk--Bleak--Matucci--Zaremsky; this asks for arbitrary peripheral subgroups that are themselves in the Boone--Higman class.
  boone-higman-conjecture: that quantifies over all decidable finitely generated groups; this is one permanence property of the class, which the conjecture implies.
  bh-class-free-products-iff-joint-embedding-and-free-z: that characterizes free-product closure, which is the special case of this statement where G is a free product of its peripheral subgroups.
artifacts:
  - research/artifacts/gq-bh-bh-relhyp-attack.md
---

**OPEN.** Let `G` be a finitely generated group with solvable word problem,
hyperbolic relative to finitely generated subgroups `P_1, ..., P_m`, each of which
embeds in a finitely presented simple group. Then `G` embeds in a finitely presented
simple group.

This is not an item of Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356, Problem 5.3
(checked against the arXiv HTML of v3). It is the natural relative version of their
hyperbolic theorem.

## What is known

- **Hyperbolic peripherals.** If every `P_i` is hyperbolic, `G` is hyperbolic
  (standard: Osin, Mem. AMS 179 (2006); not re-read), so
  `hyperbolic-groups-satisfy-boone-higman` applies.
- **Linear inputs.** Limit groups (BBMZ survey Theorem 5.1(5)) and fundamental
  groups of finite-volume hyperbolic manifolds are relatively hyperbolic and
  finitely generated linear, so `finitely-generated-linear-groups-satisfy-boone-higman`
  covers them. For finite-volume hyperbolic 3-manifolds this is also survey
  Theorem 5.1(8). So the statement adds nothing for these named families.
- **Free products in the permutational class.** Belk--Fournier-Facio--Hyde--Zaremsky,
  arXiv:2503.21882 (abstract), prove that the permutational Boone--Higman property
  is closed under free products. That settles the case `G = P_1 * ... * P_m` with
  all `P_i` in the permutational class.

## Consequences and reductions (landed)

- **At least as hard as free-product closure.**
  `rel-hyperbolic-bh-permanence-implies-free-product-closure`: this statement implies
  that the Boone--Higman class is closed under free products, hence joint
  embedding for finitely presented simple groups and `U * Z ∈ 𝓑`. Those are OPEN.
- **Finitely presented simple peripherals suffice.**
  `rel-hyperbolic-groups-embed-with-fp-simple-peripherals`: it is enough to prove
  the statement when every `P_i` is a finitely presented simple group (and then
  `G` may be taken finitely presented).

## Attempts

**Attempt 1 (bh-relhyp, 2026-09-18): germ extension over a relative boundary. Not
constructed.**
- *Why the BBMZ proof does not transfer directly.* Their embedding goes through a
  full contracting rational similarity group (their Theorems B, C, E), and they
  note (§1.3, with their Proposition 5.5) that every germ group of such a group is
  virtually cyclic. The hyperbolicity is used in their contracting lemma (Lemma
  4.19). A peripheral subgroup of `G` that is not virtually cyclic would have to act
  without contributing a large germ group at any point, and nothing in their
  construction arranges that. This part is a reading of their method, not a
  theorem.
- *The route that remains.* Belk--Hyde--Matucci, arXiv:2407.03149 (TeX read; label
  `cor:MainFinitenessCorollary`), allow a finite germ extension `E` of a base `B` to
  have germ groups larger than those of `B`: condition (3) there asks only that
  `(B)_p ⊴ (E)_p` with `(E)_p/(B)_p` of type `F_n`. After the reduction above the
  peripheral subgroups are finitely presented, so germ groups such as
  `(B)_p × S_i` are allowed. The missing input is:

  **(RB)** For `G` hyperbolic relative to finitely presented simple `S_1, ..., S_m`,
  find a Cantor space `X`, a faithful `G`-action on `X` and a base `B ≤ Homeo(X)`
  such that `G` lies in a finite germ extension `E` of `B` whose singular set is a
  finite union of `B`-orbits of points fixed by conjugates of the `S_i`, with germ
  groups `(E)_p ≅ (B)_p × S_i`. It must also satisfy hypotheses (1)--(2) of that
  corollary (`B` oligomorphic on the singular set, fixers of finite sets of type
  `F_2`) and the hypotheses of their simplicity theorem (label `thm:Simplicity`:
  `B` simple, locally moving, no global fixed point, same orbits as `E`).

  `B` cannot be `V` in general, since the non-parabolic part of `G` must act by
  elements that locally agree with `B`. The natural candidate is a relative
  version of BBMZ Theorem 4.1: a full contracting rational similarity group acting
  on a "relative horofunction boundary" of `G`, in which the parabolic points are
  exactly the singular points. No such construction is known here.
- *Calibration.* By `rel-hyperbolic-bh-permanence-implies-free-product-closure`,
  (RB) for `G = S * T` with `S, T` finitely presented simple would already prove
  free-product closure of the Boone--Higman class. So (RB) is a genuinely new
  input, not a formality.

## Scope

Nothing here embeds any new group in a finitely presented simple group.
