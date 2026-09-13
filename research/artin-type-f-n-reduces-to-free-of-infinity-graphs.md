---
rg: 2
id: artin-type-f-n-reduces-to-free-of-infinity-graphs
kind: claim
title: "An Artin group is of type F_n if all its free-of-infinity standard parabolic subgroups are"
---

Let `Γ` be a finite Coxeter graph on `S` and let `n ∈ {1, 2, 3, …} ∪ {∞}`. Call
`T ⊆ S` free of infinity if `m_st < ∞` for all `s, t ∈ T`. If the standard parabolic
subgroup `A_T` is of type `F_n` for every free-of-infinity `T ⊆ S`, then `A_Γ` is of
type `F_n`.

Since a standard parabolic subgroup of an Artin group is the Artin group of the induced
subgraph (van der Lek; L. Paris, arXiv:1211.7339, Theorem 5.4), it follows that every
Artin group is of type `F_n` if and only if every Artin group whose Coxeter graph has
only finite labels is of type `F_n`. For `n = ∞` this reduces Zaremsky Problem 1.5 to
free-of-infinity graphs (route `artin-f-infinity-from-free-of-infinity-case`).

This is the finiteness analogue of the reduction for asphericity due to G. Ellis and
E. Sköldberg (Comment. Math. Helv. 85 (2010)), recorded as Theorem 5.6 and Corollary 5.7
in Paris's survey; see also E. Godelle and L. Paris, arXiv:1007.1365. The proof route
`artin-type-f-n-reduces-to-free-of-infinity-graphs-proof` splits `A_Γ` along an
infinite label and applies the graph-of-spaces construction with finite skeleta.
