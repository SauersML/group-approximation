---
rg: 2
id: unimodular-dissections-have-egyptian-fraction-volumes
kind: claim
title: The pieces of every unimodular dissection of the standard simplicial cone have reciprocal height products summing to one, so each piece count admits only finitely many dissections
distinct_from:
  rational-projective-full-groups-are-finitely-presented: that is the finite-presentation gate for the integral projective full groups; this is a counting identity for the unimodular dissections that index the cells of any Brown or Stein complex for those groups, and it supplies the cocompactness half of such an argument.
  rank-one-rational-projective-full-group-is-flip-v: that identifies the rank-one group through the Stern–Brocot tree; in rank one this identity is the classical Farey identity, and here it holds in every dimension, where no tree exists.
---

**ESTABLISHED** (lane bh-free-54, 2026-09-18). Lane proof below; elementary, not
independently reviewed. No priority claimed; the identity is the projective form of
a volume computation that is surely classical (compare Mundici's denominator
measure on unimodular triangulations, not read here).

## Setting

- Let `m ≥ 1`, `Δ = cone(e_0, …, e_m) ⊂ R^{m+1}`, and `h(x) = x_0 + ⋯ + x_m`.
- A *unimodular dissection* of `Δ` is a finite set of cones
  `C_i = cone(v_{i,0}, …, v_{i,m})` such that:
  - each `v_{i,j}` is a primitive integral vector;
  - each `|det(v_{i,0}, …, v_{i,m})| = 1`;
  - the interiors of the `C_i` are pairwise disjoint;
  - the `C_i` cover `Δ`.
- Equivalently, it is a partition of the clopen `Δ ⊂ Ŝ_m` into translates `gΔ`,
  `g ∈ GL_{m+1}(Z)`, as in `closed-mcg-embeds-in-rational-projective-full-group`.
  T-junctions are allowed.
- The *weight* of a piece is `w(C_i) = 1 / (h(v_{i,0}) ⋯ h(v_{i,m}))`.

## Statement

1. **Identity.** For every unimodular dissection, `Σ_i w(C_i) = 1`.
2. **Finiteness.** For each `k` there are only finitely many unimodular dissections
   of `Δ` with `k` pieces.
   - Every vertex `v` of such a dissection has `h(v) ≤ D_k`, the largest
     denominator occurring in a `k`-term representation `1 = Σ 1/N_i` by unit
     fractions.
   - `D_2 = 2`, `D_3 = 6`, `D_4 = 42`. In general `D_k = s_k − 1` for Sylvester's
     sequence `2, 3, 7, 43, …` (Curtiss 1922; recalled, not re-read). Only
     finiteness is used.
3. **Exact union test.** A unimodular cone `T ⊆ Δ` is a union of pieces of a
   unimodular dissection if and only if the weights of the pieces contained in `T`
   sum to `w(T)`.

## Proof

1. **Identity.**
   - `h` is linear and positive on `Δ ∖ 0`.
   - For a unimodular cone `C = cone(v_0, …, v_m) ⊆ Δ`, the slice `C ∩ {h ≤ 1}` is
     the simplex `conv(0, v_0/h(v_0), …, v_m/h(v_m))`. Its volume is
     `|det(v_0, …, v_m)| / (m! ∏ h(v_j)) = w(C)/m!`.
   - The pieces have disjoint interiors and cover `Δ`, so their slices tile
     `Δ ∩ {h ≤ 1} = conv(0, e_0, …, e_m)` up to measure zero. That simplex has
     volume `1/m!`.
2. **Finiteness.**
   - **Finitely many representations.** Suppose `q = Σ_{i=1}^k 1/N_i` with `q > 0`
     rational and `N_1 ≤ ⋯ ≤ N_k`. Then `N_1 ≤ k/q`. Removing `1/N_1` leaves a
     `(k−1)`-term representation of `q − 1/N_1`, and `k = 1` is trivial. By
     induction on `k`, `1` has finitely many `k`-term representations.
   - **Heights are bounded.** By part 1, the weights of a `k`-piece dissection form
     such a representation with `N_i = ∏_j h(v_{i,j})`. Every factor is at least 1,
     so each vertex has `h(v) ≤ N_i ≤ D_k`.
   - **Finitely many dissections.** There are finitely many primitive
     `v ∈ Δ ∩ Z^{m+1}` with `h(v) ≤ D_k`. Hence there are finitely many candidate
     pieces, and finitely many `k`-element sets of them.
3. **Union test.** Apply part 1's volume computation inside `T`.
   - The pieces contained in `T` have disjoint interiors.
   - Their slices have total volume `w(T)/m!` if and only if they cover the slice of
     `T`, and hence cover `T`, since both sides are closed cones.
   - A piece that meets the interior of `T` but is not contained in `T` would leave
     part of `T` uncovered by contained pieces. So equality forces every piece
     meeting `int T` to lie inside `T`.

## Calibration: `m = 1`

- Pieces are `cone(v, w)` for consecutive Farey vectors, and `h` is the Farey
  denominator.
- The identity reads `Σ 1/(q q') = 1` over consecutive fractions of a Farey
  partition of `[0, 1]`. This is the telescoping of `a'/q' − a/q = 1/(q q')`
  (classical).

## Uses

- **Cocompactness.** Let `P` be the poset of labelled unimodular partitions of
  `Ŝ_m` (Attempt 1 of `rational-projective-full-groups-are-finitely-presented`),
  filtered by the number of pieces. Then `𝒯_m` acts on each sublevel set with
  finitely many orbits of simplices. The group is transitive on vertices of each
  height, and a chain below a vertex of height `n` is a sequence of coarsenings,
  each given by finitely many dissections with at most `n` pieces, by part 2.
- **Search.** Part 3 gives an exact, purely arithmetic test for mergeable sets of
  pieces. It is the test used in the prime-dissection search recorded on
  `unimodular-dissection-operad-has-finite-type`.

## Lesson for general BH

- **Bounded pieces, bounded vertices.** In any Thompson-like host built from an
  arithmetic groupoid (germs of `GL_n(Z)` on a rational Cantorization), a
  translation-invariant volume makes the pieces of an `n`-piece refinement
  arithmetically bounded. So the cocompactness half of Brown's criterion is
  automatic in every dimension.
- **What remains.** The descending-link or operad-finiteness half is then the only
  input left.
- **A transferable tool.** Any volume invariant of the germ groupoid, such as the
  Farey identity or its higher-dimensional form here, gives cocompactness. So the
  finiteness problem for such hosts is always purely local combinatorics.
