---
rg: 2
id: leavitt-centralizer-units-are-elementary-in-rank-three
kind: claim
title: A unit that commutes with a binary Leavitt pair is an elementary matrix in rank three; so Q^x scalars are central in E_m(S)
distinct_from:
  q-coefficient-leavitt-tensor-unit-groups-are-fp: that records the scalar obstruction under GL_N = E_N (K_1 = 0); this proves without any K-theory that scalars commuting with a Leavitt pair are elementary, so the obstruction applies to E_m of every ring containing Q and a Leavitt pair.
  leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1: that uses the same elementary factorization of the swap matrix W at the Steinberg level; this uses it at the matrix level for units.
artifacts:
  - research/artifacts/gq-steinberg-q-e-n-of-resolvent-ring-status.md
---

**ESTABLISHED (2026-09-17)** through
`leavitt-centralizer-units-are-elementary-in-rank-three-proof`. Lane proof
(`gq-steinberg-q`), elementary, not independently reviewed.

**Statement.** Let `S` have a Leavitt pair `x_1, x_2, y_1, y_2`, and let `u ∈ S^x` commute
with all four elements. Then `diag(u, 1, 1) ∈ E_3(S)`, and so `diag(u, 1, …, 1) ∈ E_m(S)`
for every `m >= 3`. If `Q ⊆ S` is a unital subring, then `Q^x · I_m` lies in the centre of
`E_m(S)` for every `m >= 3`. That subgroup is not finitely generated.

**Consequence (scalar obstruction).** For a finitely presented ring `S ⊇ Q` with a Leavitt
pair, such as `R_L`, and `m >= 3`, the groups `E_m(S)` and `E_m(S)/(Q^x · I_m)` are not
both finitely presented. The reason: a quotient of a finitely presented group by a central
subgroup that is not finitely generated is not finitely presented, as recorded in
`q-coefficient-leavitt-tensor-unit-groups-are-fp`.

## Proof

Let `W = [[y_1,0,0],[y_2,0,0],[0,x_1,x_2]]`. By Change 1 of
`leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1` with `N = 1`,

    e_23(-y_2) e_13(-y_1) e_32(x_2) e_31(x_1) · W · e_12(-x_1) e_13(-x_2) = [[0,-1,0],[0,0,-1],[1,0,0]],

and the right side lies in `E_3(Z)`. So `W ∈ E_3(S)`. The inverse of `W` is
`[[x_1,x_2,0],[0,0,y_1],[0,0,y_2]]`.

1. **Conjugation doubles u.** Put `d = diag(u,1,1)`. Direct multiplication, using `y_s x_t = δ_st`,
   `x_1 y_1 + x_2 y_2 = 1` and that `u` commutes with the pair, gives
   `W d W^(-1) = diag(u, u, 1)`.
2. **One coordinate.** `diag(1, u, 1) = (W d W^(-1)) d^(-1) = W · (d W^(-1) d^(-1))`.
   Conjugating an elementary matrix by the diagonal `d` gives an elementary matrix:
   `d e_ij(r) d^(-1) = e_ij(d_i r d_j^(-1))`. So `d W^(-1) d^(-1) ∈ E_3(S)`, and
   `diag(1,u,1) ∈ E_3(S)`.
3. **Other positions.** Conjugating by the signed permutation `[[0,1,0],[-1,0,0],[0,0,1]] ∈ E_3(Z)`
   moves `u` to position 1. Stabilizing gives `diag(u,1,…,1) ∈ E_m(S)`.
4. **Scalars.** `q I_m` is a product of `m` such matrices. It is central because `q` is
   central in `S`.
