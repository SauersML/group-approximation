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
- Candidate families to test: groups of type `FP` that are not finitely
  presented and have no known acyclic level-set model. Examples are Leary's
  `G_L(S)` in cases where the universal cover of `L` fails to be acyclic
  (hypotheses being checked from arXiv:1512.06609), and the graphical
  small-cancellation groups of Brown–Leary (arXiv:2004.04550).
