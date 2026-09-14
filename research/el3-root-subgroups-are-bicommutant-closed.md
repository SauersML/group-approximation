---
rg: 2
id: el3-root-subgroups-are-bicommutant-closed
kind: claim
title: Over a unital ring with centre F_2, each root subgroup of EL_3 is its own double centralizer, while the row and column subgroups are abelian and self-centralizing
artifacts:
  - research/artifacts/sk-rigidity-f2-2026-09-13.md
---

Let `R` be a unital associative ring with `Z(R) = F_2`, let `G = EL_3(R)`, and write `A_ij = {e_ij(r) : r ∈ R}` for
the root subgroups, `Row_i = {I + Σ_{j≠i} E_ij b_j}` and `Col_j = {I + Σ_{i≠j} E_ij b_i}`.

1. `C_{GL_3(R)}(A_12) = {g : g_11 = g_22 = 1, g_21 = g_31 = g_23 = 0}`, and likewise for the other five root
   subgroups after permuting indices.
2. `C_G(C_G(A_ij)) = A_ij`. So every root subgroup is bicommutant closed.
3. Every `Row_i` and every `Col_j` is abelian and satisfies `C_G(Row_i) = Row_i`, `C_G(Col_j) = Col_j`.
4. `A_ij = Row_i ∩ Col_j`.

By (3) and (4), root subgroups are never maximal abelian, so the maximal members of the family of
bicommutant-closed abelian subgroups of `G` are not the root subgroups. This is a firewall against the natural
lattice-theoretic characterization of root subgroups, and it complements firewall F-EA of
`subshift-el3-isomorphisms-are-standard-over-f2`.

`R_X = LC(X,F_2) ⋊_T Z` for an infinite minimal subshift `X` satisfies `Z(R_X) = F_2`, so all four statements apply
to the group `G_X` of `simple_kazhdan_sofic_group.tex`.
