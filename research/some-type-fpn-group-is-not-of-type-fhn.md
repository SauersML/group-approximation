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
- Dead candidate: Leary's open case (arXiv:1512.06609, checked from the TeX
  source 2026-09-13): `G_L(S)` with `L` a finite acyclic flag complex,
  `π_1(L)` of type `FP`, `ℤ − S` finite and nonempty, and `L̃` not acyclic.
  Leary shows these are `FP` and writes "we do not know whether `G_L(S)` is
  necessarily `FH(R)`". At every finite `n` they are of type `FH_n` over `ℤ`
  (`leary-groups-with-cofinite-s-are-type-fhn`, unreviewed). Leary's other
  cases were already `FH_n` whenever `FP_n`. So Leary's family gives no
  separation of `FP_n` from `FH_n`; it can only bear on `FP` versus `FH`.
- The obstruction has to be of a new kind. By
  `type-fh3-iff-fp3-and-superperfect-kernel-over-fp-group`, a witness at
  `n = 3` is an `FP_3` group such that every finitely presented `Q ↠ G` with
  perfect kernel has `H_2(ker) ≠ 0`. By
  `isolated-type-fn-vertex-stabilizers-give-type-fhn`, the witness admits no
  cocompact action on a 2-acyclic complex with only isolated type-`F_3`
  singular vertices.
- Not candidates: Brown–Leary's graphical small-cancellation groups `G(S)`
  (arXiv:2004.04550) are stated there to be of type `FH`, of cohomological
  dimension two.
