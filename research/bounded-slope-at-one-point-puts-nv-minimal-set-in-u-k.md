---
rg: 2
id: bounded-slope-at-one-point-puts-nv-minimal-set-in-u-k
kind: claim
title: If a finitely generated subgroup of nV has bounded slope cocycle at one point of a minimal closed invariant set, that minimal set is a finite orbit inside the locally virtually trivial part U_K
distinct_from:
  finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite: that shows a finitely generated subgroup is finite iff the slope is bounded at every point of the cube, by brick induction over words; this uses the bound at a single point of one minimal set and concludes only about that minimal set, through a Gottschalk–Hedlund argument on the skew product.
  kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures: that builds a measurable integer potential from an invariant measure using (T); this builds a continuous potential on a minimal set from one bounded orbit, without (T) and without any measure.
  minimal-cantor-crossed-products-have-internal-cancellation: that route uses the classical Gottschalk–Hedlund theorem for real cocycles of a single homeomorphism; this is the group version for the Z^n-valued slope cocycle of a subgroup of nV, with a brick-permutation conclusion.
artifacts:
  - research/artifacts/kazhdan-nv-displacement-gap-2026-09-17.md
---

**ESTABLISHED** by `nv-slope-gottschalk-hedlund-proof` (agent-verified only, no referee
pass as of 2026-09-17).

## Statement

Let `K <= nV` be finitely generated, `s: K x C^n -> Z^n` the slope cocycle, and
`Z ⊆ C^n` a minimal closed `K`-invariant set. If `sup_{g∈K} |s(g,x)| < ∞` for some
`x ∈ Z`, then there are a locally constant `F: Z -> Z^n` with `s(g,y) = F(y) - F(gy)` on
`Z`, and a finite family of bricks covering `Z` that `K` permutes canonically; hence
`Z ⊆ U_K` and `Z` is a finite orbit.

**Corollary.** On every minimal set that is not a finite orbit, in particular on every
minimal subset of `Z_K` for an infinite Kazhdan `K`, the slope cocycle is unbounded along
every orbit.

## Consequence for the target

A counterexample to `minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures`
has unbounded slopes along every orbit of its measure-free minimal sets. Bounded height
selections of bricks on such sets cannot exist, and any potential for the slope cocycle
there has infinite range on every orbit. Details: artifact Section C.
