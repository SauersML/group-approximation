---
rg: 2
id: artin-word-problem-reduces-to-free-of-infinity-graphs
kind: claim
title: An Artin group has solvable word problem when every maximal free-of-infinity standard parabolic subgroup does
distinct_from:
  artin-type-f-n-reduces-to-free-of-infinity-graphs: that transfers the finiteness property F_n from free-of-infinity graphs to all graphs; this transfers solvability of the word problem, an algorithmic property, using normal forms in amalgams and membership algorithms for parabolic subgroups.
  artin-k-pi-1-reduces-to-free-of-infinity-parabolics: that transfers asphericity of the Salvetti complex through cube complexes; this transfers the word problem through amalgamated products, and neither statement implies the other.
  artin-k-pi-1-from-maximal-free-of-infinity-subsets: that is the K(π,1) conjecture assembled from maximal free-of-infinity subsets; this is the word problem assembled from the same subsets, and type F does not force a solvable word problem.
  every-artin-group-has-solvable-word-problem: that is the open statement for every Artin group; this only moves the word problem from the maximal free-of-infinity parabolic subgroups to the whole group.
---

Let `Γ` be a Coxeter graph on a finite set `S`, with labels `m_st ∈ {2, 3, …, ∞}`. For
`X ⊆ S` let `Γ_X` be the induced graph. Call `X` *free of infinity* when `m_st < ∞` for
all `s, t ∈ X`.

**Statement.** Suppose that, for every maximal free-of-infinity subset `X ⊆ S`, the
Artin group `A_{Γ_X}` has solvable word problem. Then `A_Γ` has solvable word problem.

The case where every free-of-infinity Artin group has solvable word problem is Theorem C
of E. Godelle and L. Paris, *Basic questions on Artin-Tits groups*, arXiv:1105.1048. The
form for a single graph comes from reading that proof. The argument, with the quotes it
uses, is the route `artin-word-problem-free-of-infinity-citation`.

The induction step splits `A_Γ` along a label `m_st = ∞` as
`A_{S∖{s}} *_{A_{S∖{s,t}}} A_{S∖{t}}`. It combines the normal form theorem for amalgams
with the Godelle–Paris algorithm that decides membership in a standard parabolic
subgroup and rewrites a member in its own generators.

So for the word problem, the Artin groups with infinite labels add nothing beyond their
free-of-infinity parabolic subgroups. The remaining question is
`every-free-of-infinity-artin-group-has-solvable-wp`.
