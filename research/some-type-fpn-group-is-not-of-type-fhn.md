---
rg: 2
id: some-type-fpn-group-is-not-of-type-fhn
kind: claim
title: "For some n at least 3, some group of type FP_n has no proper cocompact action on an (n-1)-acyclic complex"
distinct_from:
  every-type-fpn-group-is-of-type-fhn: that claim asserts the implication FP_n implies FH_n for all n; this is its negation, witnessed by one n and one group
---

There are `n ≥ 3` and a group `G` of type `FP_n` (over `ℤ`) such that `G`
admits no cellular action on an `(n−1)`-acyclic CW complex with finite cell
stabilizers and finitely many orbits of cells.

This is the negative answer to Zaremsky Problem 1.4
(`zaremsky-1-04-type-fpn-equals-type-fhn`). The bound `n ≥ 3` is forced,
because the implication holds for `n ≤ 2`.

## Attempts

- At `n = 3` a witness is a group of type `FP_3` that is not `Q/P` for any
  finitely presented `Q` and superperfect `P` (root's Attempts). An invariant
  would have to see every finite presentation with perfect kernel at once.
  Low-degree homology does not obstruct: a superperfect kernel gives
  `H_k(Q; M) ≅ H_k(G; M)` for `k ≤ 2` and all `ℤG`-modules `M`, and this is
  compatible with `FP_3`. No invariant found yet.
- Main candidate family, the open case stated by Leary (arXiv:1512.06609,
  checked from the TeX source 2026-09-13): `G_L(S)` with `L` a finite
  `R`-acyclic flag complex, `ℤ − S` finite and nonempty, and `L̃` not
  acyclic. Leary shows these are `FP(R)` and writes "we do not know whether
  `G_L(S)` is necessarily `FH(R)`". His method would give `FH` from a
  `π_1(L)`-equivariant map from the vertex link to an acyclic free cocompact
  `π_1(L)`-complex. By `type-fh3-iff-fp3-and-superperfect-kernel-over-fp-group`,
  a separation at `n = 3` would need to rule out every finitely presented
  `Q ↠ G_L(S)` with superperfect kernel.
- Not candidates: Brown–Leary's graphical small-cancellation groups `G(S)`
  (arXiv:2004.04550) are stated there to be of type `FH`, of cohomological
  dimension two.
