---
rg: 2
id: artin-f-infinity-from-free-of-infinity-case
kind: route
title: Type F_infinity for every Artin group follows from the case of graphs with only finite labels
target: every-artin-group-is-type-f-infinity
requires:
  - artin-type-f-n-reduces-to-free-of-infinity-graphs
  - every-free-of-infinity-artin-group-is-type-f-infinity
---

Let `Γ` be a finite Coxeter graph on `S`. For each free-of-infinity `T ⊆ S`, the
standard parabolic subgroup `A_T` is the Artin group of the free-of-infinity graph `Γ_T`
(van der Lek; arXiv:1211.7339, Theorem 5.4), so it is of type `F_∞` by
`every-free-of-infinity-artin-group-is-type-f-infinity`. Then
`artin-type-f-n-reduces-to-free-of-infinity-graphs` with `n = ∞` shows that `A_Γ` is of
type `F_∞`.

The converse is trivial, so this route is an equivalence. It is a genuine narrowing,
not a restatement: the prerequisite says nothing about graphs with infinite labels, and
the passage to them is the splitting `A_Γ = A_{S∖s} *_{A_{S∖{s,t}}} A_{S∖t}` along a label
`m_st = ∞`.
