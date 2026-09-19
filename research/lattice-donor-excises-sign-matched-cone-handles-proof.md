---
rg: 2
id: lattice-donor-excises-sign-matched-cone-handles-proof
kind: route
target: lattice-donor-excises-sign-matched-cone-handles
requires:
  - near-exact-tuples-saturate-linear-conversion-defect
title: Cutting along a simple loop and its flat lattice copy splits the cone point in two without changing the excess, and the sign-matched partner loop and its copy then join the same two halves
---

Notation as in the claim. The pair lives on `Omega ⊔ T`, where `T` carries the translations of `Z^2/Lambda`, with
`Lambda = <u, w>`. Padding by a commuting pair changes neither the excess nor `rho`.

## 0. Corners, fans and swaps

Each square has four corners. A vertex is a class of corners under the identifications made by the gluings. Its cone
angle is `(pi/2)·#corners`, and its excess is `angle/2pi - 1`. Summing over the vertices of a surface with `F` squares
gives the total excess

`E = sum_v (theta_v/2pi - 1) = F/2 - #vertices`,

because the angles add up to `2 pi F`. This equals `rank([b, c] - I)`. So a surgery that keeps the squares changes
the excess by exactly minus the change in the number of vertices.

The corners of a vertex `v` lie in one cyclic order: rotate around `v` from square to square across the edges at `v`.
A path that passes through `v` once, entering along edge `e_in` and leaving along `e_out`, cuts this cycle into two
arcs:
- the *left fan*, counterclockwise from `e_out` to `e_in` reversed;
- the *right fan*, the rest.

The same holds at the base point of a loop, with `e_out` its first edge and `e_in` its last edge.

A path is recorded as a sequence of pairs (square on its left, side). Two paths with the same word use the same side
at every step. Let `P = (e_1, ..., e_m)` and `P' = (e'_1, ..., e'_m)` be such paths, with no edge in common. Write
`l_i, r_i` for the squares to the left and right of `e_i`, and likewise `l'_i, r'_i`. The swap glues `l_i` to `r'_i`
and `l'_i` to `r_i` across the side of `e_i`. Each glued pair uses the same generator, so the result is again a
permutation pair. Only corner identifications across the edges `e_i, e'_i` change.

## 1. The first swap is excess-neutral

Write `v_0 = A, v_1, ..., v_(m-1)` for the vertices of `alpha` and `v'_0 = 0, ..., v'_(m-1)` for those of `alpha'`.
All of them are distinct, by simplicity, and `alpha` lies in `S` while `alpha'` lies in `T`. Let `L_i, R_i` be the fans
of `alpha` at `v_i`, and `L'_i, R'_i` those of `alpha'` at `v'_i`.

The edge `e_i` runs from `v_(i-1)` to `v_i` (indices mod `m`). Before the swap, the corners of `l_i` and `r_i` at the
start of `e_i` were identified. The corner of `l_i` there is the last corner of `L_(i-1)`, and the corner of `r_i` is
the first corner of `R_(i-1)`. The same holds at the end of `e_i`. After the swap:
- the extreme corners of `L_j` are identified with the extreme corners of `R'_j`;
- those of `L'_j` are identified with those of `R_j`.

No other identification at these vertices changes, because no other edge of `alpha` or `alpha'` meets `v_j` or `v'_j`.
So the `2m` vertices `v_j, v'_j` are replaced by the `2m` vertices `L_j ∪ R'_j` and `L'_j ∪ R_j`. No other vertex
changes. The number of vertices is the same, so `E` is unchanged.

The two halves of `A` are `A_L = L_0 ∪ R'_0` and `A_R = L'_0 ∪ R_0`.

## 2. Where `beta` and `beta'` run after the first swap

The edges of `beta` are not edges of `alpha`, so their gluings are unchanged. The interior vertices of `beta` are not
on `alpha`, so the gluings around them, which the turns of the word use, are unchanged too. So `beta` is still a path
with the same word in the new surface `S_1`. Its interior vertices are unchanged vertices of `S`, distinct from
`A_L` and `A_R`. The same holds for `beta'` in the `T`-part, since by (H2) `beta'` meets `alpha'` only at `0`.

*Endpoints of `beta`.* Take `det(u, w) > 0`. By (H1), the first edge of `beta` leaves `A` inside `R_0`, so `beta`
starts at the class containing `R_0`, which is `A_R`. It returns from inside `L_0`, so it ends at `A_L`.

*Endpoints of `beta'`.* In the flat torus `T`, `alpha'` and `beta'` are simple closed curves in the classes `u` and
`w`. Their algebraic intersection number is `det(u, w)/covol(Lambda) = +1`, since `Lambda = <u, w>`. They meet only at
`0`, so they cross there exactly once, and positively: `beta'` goes from the right side of `alpha'` to its left. (If
they only touched at `0`, the intersection number would be 0.) So `beta'` leaves `0` inside `L'_0` and returns from
inside `R'_0`. It starts at `A_R`, which contains `L'_0`, and ends at `A_L`, which contains `R'_0`.

For `det(u, w) < 0`, both signs flip. Then `beta` and `beta'` both run from `A_L` to `A_R`.

## 3. The second swap lowers the excess by 2

Now `beta` and `beta'` have the same word and no common edge. Their interior vertices are pairwise distinct, and they
share both endpoints: `A_R` (start) and `A_L` (end), which are distinct vertices.

*Interior vertices.* Exactly as in Section 1, the `2(m' - 1)` interior vertices are replaced by `2(m' - 1)` vertices.

*The start `A_R`.* Its corner cycle is cut by the two first edges into two arcs:
- `X`, counterclockwise from the first edge of `beta` to the first edge of `beta'`;
- `Y`, the rest.

The two extreme corners of `X` are the corner of `l_1` (left of `beta`) and the corner of `r'_1` (right of `beta'`).
The swap identifies them. The extreme corners of `Y` are those of `l'_1` and `r_1`, which are identified likewise.
All other identifications at `A_R` stay as they were. So `A_R` becomes two vertices, `X` and `Y`, both nonempty.

*The end `A_L`.* By the same argument at the last edges, `A_L` becomes two vertices.

The number of vertices therefore goes up by exactly 2, so `E` drops by exactly 2. Since `E` is even, the new excess
is `E - 2 >= 0`.

## 4. Cost and profile

Each corresponding pair of edges swaps two values of one generator: `b` for vertical edges, `c` for horizontal ones.
Both swaps together multiply `b` by at most `V_alpha + V_beta` transpositions, and `c` by at most `H_alpha + H_beta`.
Rank is subadditive, so `rank(b_2 - b) <= V_alpha + V_beta` and `rank(c_2 - c) <= H_alpha + H_beta`. The Lipschitz
bound `rank([b'^s, c'^t] - [b^s, c^t]) <= 2 s rank(b' - b) + 2 t rank(c' - c)` comes from telescoping the four
factors, as in Lemma B of `near-exact-tuples-saturate-linear-conversion-defect-proof`. It gives
`rho(b_2, c_2) <= rho(b, c) + 2(|alpha| + |beta|)`.

The donor has area `|det(u, w)| <= |u|_1 |w|_1 <= |alpha| |beta|`. QED.

## 5. Checks

- `handle_check.py` enumerates every pair of simple loops of length at most 5 at a cone point that satisfies (H2),
  on the surfaces listed in the claim. The first swap is neutral in all 8298 pairs. The drop by 2 happens exactly on
  the 600 pairs with (H1), so the sign condition is sharp.
- `blocks.py` builds excised `k x l` blocks. The handle made of the hole's bottom edge and left edge (holonomies
  `(k, 0)` and `(0, l)`) satisfies (H1) and (H2), and it closes each case at total length `k + l`.
