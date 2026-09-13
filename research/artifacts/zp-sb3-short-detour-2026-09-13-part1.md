# SB_3 and short-detour enumerations, part 1: setup and the link lemma

Lane z1-03-qi-fn, 2026-09-13. Target: `some-non-f3-group-has-a-short-detour-enumeration`, tested on the
Stallings–Bieri group SB_3, which is finitely presented and not of type F_3. If SB_3 has a short-detour
enumeration, the geodesic reading of Zaremsky Problem 1.3 has answer no
(`short-detour-enumeration-gives-contractible-qi-2-complex`). Status: UNREVIEWED WORK IN PROGRESS.

## 1. Model

- T is the Cayley tree of F_2 = ⟨a, b⟩, with height h(a) = h(b) = 1. Every vertex has two up-edges (a, b)
  and two down-edges (a^{-1}, b^{-1}).
- SB_3 = ker(F_2^3 → Z), where every generator maps to 1. It acts simply transitively on the height-0
  vertices of T^3 (h = h_1 + h_2 + h_3).
- Generating set S = { x_i y_j^{-1} : i ≠ j, x, y ∈ {a, b} } (24 elements). Any element of ker φ is a word
  of total exponent zero, and it is a product of elements x z^{-1} and z^{-1} x. For i ≠ j these are in S,
  since the factors commute. For i = j: a_1 b_1^{-1} = (a_1 a_2^{-1})(a_2 b_1^{-1}).
- The Cayley graph Γ has vertices v = (x_1, x_2, x_3) with Σ h(x_i) = 0. Edges are moves (i ↑ u, j ↓ d):
  an up-edge u at x_i together with a down-edge d at x_j, i ≠ j. Each edge is a square of T^3 with
  corners at heights −1 and +1.

## 2. Candidate enumeration

- o = (e, e, e). d_i(v) = d_T(x_i, e). Order key K(v) = (F(v), (d_1, d_2, d_3)), where
  F = d_1^2 + d_2^2 + d_3^2, compared lexicographically; ties with equal key are broken arbitrarily.
- Only vertices with strictly smaller key are used for detours. So a detour through them is available
  in every tie-breaking, and that is conservative.
- A neighbour never has the same key as v. A move changes two coordinates by ±1 each, so F is unchanged
  only if (d_i, d_j) becomes (d_j, d_i), which changes the vector unless d_i = d_j. But then the move is
  (−1, +1) with d_i = d_j + 1, a contradiction.
- Therefore the earlier neighbours of v are exactly its neighbours of smaller key, in every tie-breaking.

## 3. The link of v

- Halves at v: 6 up-halves (tree, up-edge) and 6 down-halves. A neighbour is a pair (u, d) of an up-half
  and a down-half in different trees. There are 24 such pairs.
- If d_i ≥ 1, tree i has exactly one baseward edge, with direction σ_i ∈ {↑, ↓}. Put a(half) = 1 − 2d_i
  if the half is baseward and 1 + 2d_i otherwise. Then F(v·(u,d)) − F(v) = a(u) + a(d).
- Ties (sum 0) occur iff one half is baseward in tree i and the other is away in tree j with
  d_i = d_j + 1. The neighbour then has coordinates i, j swapped, and it is earlier iff i < j.
- Link adjacency: (u, d) ~ (u, d') when tree(d) ≠ tree(d'), and (u, d) ~ (u', d) when
  tree(u) ≠ tree(u'). (If (u, d), (u, d') are neighbours of v and d, d' lie in different trees, then
  v·(u,d')= v·(u,d)·(tree(d) ↑ d^{-1}, tree(d') ↓ d').)

**Link lemma (star).** Let M maximize d_i. Suppose σ_M = ↑, and let u* be the baseward up-half of tree M.

1. No earlier neighbour has its down-half in tree M. Both down-halves there are away, so
   a(u) + a(d) ≥ (1 − 2d_i) + (1 + 2d_M) > 0.
2. Every earlier (u, d) with u ∉ tree M is adjacent in the link to (u*, d). Since
   a(u*) = 1 − 2d_M ≤ a(u), (u*, d) is earlier as well, with ties handled by the index rule (to be
   rechecked case by case).
3. Pairs (u*, d), (u*, d') with d, d' in different trees are adjacent.

So the earlier link is connected unless the only earlier star vertices through u* use the two
down-halves of a single tree j, and no earlier vertex connects them. That needs:

- d_M ≥ d_j + 2;
- the third tree l has σ_l ∈ {↑, none} and d_l ∈ {d_M − 1, d_M}, with the tie rule failing.

In this case there are two ways to connect them.

- **Length-2 detour.** Put p = v·u*, at height +1. The vertex (x_M u* x, x_j, x_l), with x the other
  down-edge at p_M, is adjacent to both. It is strictly earlier iff x is baseward at p_M.
- **Otherwise.** The detour must have length ≥ 3, or the enumeration fails there. Part 2 records the
  computer census (MSI, `sb3_detour.py`) and the case analysis.

The symmetric case σ_M = ↓ is the same with the roles of up and down exchanged.

## 4. Census of the quadratic key (MSI, `sb3_detour.py`, 2026-09-13)

This checks bullets 1–2 for every v ≠ o whose coordinates all have length ≤ R0, using detours of length
≤ L through strictly earlier vertices.

| L | R0 | vertices checked | failures | no earlier neighbour |
|---|----|------------------|----------|----------------------|
| 2 | 2  | 820              | 61       | 16                   |
| 3 | 2  | 820              | 16       | 16                   |
| 2 | 3  | 14908            | 3786     | 336                  |

**The key F = Σ d_i^2 is dead.** The vertices with no earlier neighbour include v = (aB, aB, aB): all
coordinates have length 2, and every baseward edge is an up-edge (σ = ↑ in all three trees). Every move
pairs a baseward up-step in one tree with an away down-step in another, so the distance vector becomes a
permutation of (1, 3, 2) and F goes from 12 to 14. This is a strict local minimum.

The same point is a plateau for the ℓ^1 key Σ d_i. A symmetric monotone key of the distance vector must
satisfy both:

- F(1, 3, 2) < F(2, 2, 2), so a spread-out vector is earlier;
- F(1, d − 1, 0) < F(0, d, 0), so a concentrated vector is later. Otherwise (e, x, e) is a local minimum.

So the key must depend on more than the distance vector, or the enumeration must be built adaptively.

Next test: a greedy exhaustion of {Σ d_i ≤ R}. Repeatedly add any vertex adjacent to the current set
whose earlier neighbours are L-connected in it, and record where it gets stuck.
