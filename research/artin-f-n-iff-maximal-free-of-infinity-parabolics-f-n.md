---
rg: 2
id: artin-f-n-iff-maximal-free-of-infinity-parabolics-f-n
kind: claim
title: "An Artin group is of type F_n if and only if every maximal free-of-infinity standard parabolic subgroup is"
distinct_from:
  artin-type-f-n-reduces-to-free-of-infinity-graphs: that is the upward implication over all free-of-infinity subsets; this is an equivalence over the maximal ones, adding the downward implication.
  artin-k-pi-1-from-maximal-free-of-infinity-subsets: that is the upward implication for asphericity; this is the two-sided statement for finiteness length.
---

Let `Γ` be a finite Coxeter graph on `S` and `n ∈ {1, 2, …} ∪ {∞}`. Let `X_1, …, X_m` be
the maximal free-of-infinity subsets of `S` (`m_st < ∞` for all `s, t ∈ X_i`). Then

`A_Γ` is of type `F_n` ⇔ every `A_{X_i}` is of type `F_n`.

Equivalently, with `fl(G) = sup{n : G is of type F_n}`,

`fl(A_Γ) = min_i fl(A_{X_i})`  and  `fl(A_{Γ_T}) ≥ fl(A_Γ)` for every `T ⊆ S`.

**What it does for Zaremsky Problem 1.5.** Both directions are needed to turn the
free-of-infinity reduction into a statement about individual groups:

- (no route) If some Artin group is not of type `F_∞`, then there is a free-of-infinity
  graph `Γ` with `A_Γ` not of type `F_∞` and every proper standard parabolic subgroup of
  type `F_∞` (take an induced subgraph minimal for failure: it is free of infinity by the
  upward direction, and its proper parabolic subgroups are `F_∞` by minimality). Failure is
  upward closed: every graph containing `Γ` as an induced subgraph also fails. With the
  imported K(π,1) cases (`artin-groups-of-rank-at-most-four-satisfy-k-pi-1`, and dimension
  at most 3 through arXiv:2509.06914), such a minimal `Γ` has rank at least 5.
- (yes route) Type `F_∞` proved for any Artin group by a global method (a combing, a
  Helly or CAT(0) action, a semihyperbolic structure) passes to all its standard parabolic
  subgroups, including those that are not covered by that method.

Proof: route `artin-f-n-iff-maximal-free-of-infinity-parabolics-f-n-proof`.
