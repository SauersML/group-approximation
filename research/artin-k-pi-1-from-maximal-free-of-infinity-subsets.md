---
rg: 2
id: artin-k-pi-1-from-maximal-free-of-infinity-subsets
kind: claim
title: An Artin group satisfies the K(π,1) conjecture, and is of type F, when every maximal free-of-infinity standard parabolic subgroup does
distinct_from:
  artin-k-pi-1-reduces-to-free-of-infinity-parabolics: that is the Godelle–Paris hypothesis over all free-of-infinity subsets; this needs only the maximal ones, by adding the Godelle–Paris retraction corollary.
  artin-k-pi-1-passes-to-standard-parabolic-subgroups: that passes asphericity down to parabolic subgroups; this uses it to pass asphericity up from the maximal free-of-infinity pieces.
---

Let `Γ` be a finite Coxeter graph on `S`. Call `X ⊆ S` a *maximal free-of-infinity subset*
when `m_st < ∞` for all `s, t ∈ X` and no larger subset has this property. If `A_{Γ_X}`
satisfies the K(π,1) conjecture for every maximal free-of-infinity `X`, then `A_Γ` satisfies
the K(π,1) conjecture and has a finite classifying space.

**How it is used.** Each maximal free-of-infinity subset may come from a different known
class: spherical, affine, rank at most 4, dimension at most 3, commuting-pairs graph without
embedded 4-cycles, complete bipartite, Huang's tree and cycle classes. Example: let `S = P ∪ Q`,
where `Γ_P` is an affine diagram of any rank, `Γ_Q` is a diagram of dimension at most 3, the two
agree on `P ∩ Q`, and `m_st = ∞` for `s ∈ P − Q`, `t ∈ Q − P`. A free-of-infinity subset cannot
meet both `P − Q` and `Q − P`, so it lies in `P` or in `Q`, and `P, Q` are the maximal ones. So
`A_Γ` satisfies the conjecture and is of type F.

Assembled here from cited theorems; no novelty is claimed. Proof in
`artin-k-pi-1-from-maximal-free-of-infinity-subsets-proof`.
