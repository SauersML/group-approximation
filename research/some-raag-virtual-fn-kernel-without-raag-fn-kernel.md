---
rg: 2
id: some-raag-virtual-fn-kernel-without-raag-fn-kernel
kind: claim
title: Some right-angled Artin group has a finite-index subgroup mapping onto Z with kernel of type F_n, while no map of the group itself onto Z has such a kernel
distinct_from:
  raag-virtual-fn-kernel-implies-raag-fn-kernel: that is the conjecture of Zaremsky's Problem 1.19; this is its negation, and an established copy of this claim would be stamped as its refuter.
---

There are a finite flag complex `L`, an integer `n ≥ 1`, a finite-index subgroup
`H ≤ A_L` and an epimorphism `ψ: H → Z` with kernel of type `F_n`, such that no
epimorphism `A_L → Z` has kernel of type `F_n`.

This is the negative answer to Zaremsky's Problem 1.19
(`zaremsky-1-19-raag-virtual-fn-kernel-conjecture`).

## Attempts

- 2026-09-13, lane z1-19-raag-kernel, later the same day: no counterexample exists if
  `raag-finite-index-sigma-m-forces-connected-flag-complex` survives review. A kernel of type
  `F_n` on a finite-index subgroup makes `L` `(n−1)`-connected, and then `BB_L` is of type `F_n`.
  When the affirmative answer claim is established, this claim gets `refuted_by` it.
- 2026-09-13, lane z1-19-raag-kernel, earlier: the homological part of the conjecture is
  provable (Betti numbers over Malcev--Neumann division rings), so a counterexample
  needs `n ≥ 2` and a flag complex `L` whose homology vanishes through degree `n−1`
  but whose fundamental group is nontrivial and perfect. Two search spaces are
  under study: hyperplane weightings of finite covers of the Salvetti complex, and
  height functions with states (Jankiewicz--Norin--Wise) on finite-index subgroups
  of the right-angled Coxeter groups that contain `A_L` with finite index
  (Davis--Januszkiewicz).
