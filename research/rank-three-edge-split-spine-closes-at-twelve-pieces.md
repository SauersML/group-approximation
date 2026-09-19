---
rg: 2
id: rank-three-edge-split-spine-closes-at-twelve-pieces
kind: claim
title: In rank three the closure of the edge splits under minimal common refinements stops after eight classes, the largest with twelve pieces, so the edge-split operad has finite type unless some pair has an extra minimal refinement with more than twelve pieces
artifacts:
  - research/artifacts/gq-bh-free-54-spine-computation.md
distinct_from:
  edge-split-operad-satisfies-ore: that bundles Ore's condition with finite type and recorded a truncated lower bound of 16 spine elements; this computes the closure exactly within twelve pieces and finds that it stops.
  thumann-finiteness-without-finite-type: that replaces finite type by connectivity of splitting categories; here the spine itself appears finite, and the splitting categories are computed as a by-product.
  edge-split-flop-spine-elements-split-disconnectedly: that computes the splitting category of the five-piece flop elements by hand; this reproduces it by machine as the calibration and computes it for every other class.
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `edge-split-operad-satisfies-ore`.

**COMPUTED** (lane bh-free-54, 2026-09-18). The search is exact within its size bound.
Statement 1 is a finite machine computation. Statement 2 is conditional on the
hypothesis (H) below, which is open and supported by the evidence listed. This is
rank three (`m = 2`). The closed-MCG host needs rank `6g − 6`.

## Setting

- **The operad.** `𝒪_E` is the edge-split operad on `Δ = cone(e_0, e_1, e_2)`, as in
  `edge-split-operad-satisfies-ore`. Transformation classes are unlabelled edge-split
  dissections, ordered by `≥_E`.
- **The spine.** Thumann's spine (arXiv:1409.1085, Definition `79040`,
  Construction `45209`) is generated from the minimal classes (the three first splits)
  by adding minimal common upper bounds of pairs.
- **Exact bounded search.** `ub_min(A, B, N)` enumerates refinements `X` of the larger
  of `A` and `B`. It branches only in two situations:
  - over the three splits of one leaf that crosses a wall of the other element (every
    upper bound splits that leaf, and the order of splitting leaves is irrelevant);
  - when no leaf crosses a wall, over the leaves inside a piece of the other element on
    which `X` is not yet a split tree (every upper bound splits one of them).

  It stops at the first `X ≥_E A, B`. Every upper bound with at most `N` pieces lies
  above a solution found, so the minimal ones with at most `N` pieces are found
  exactly.

## Statement

1. **Closure within twelve pieces (computed).** Let `𝒮` be the smallest `S_3`-closed set
   that contains the three first splits and every minimal common upper bound with at
   most 12 pieces of any two of its elements.
   - Up to `S_3`, `𝒮` has **8 classes**, with 2, 5, 5, 6, 7, 8, 10 and 12 pieces. The
     6-piece class is the barycentric fan. The two 5-piece classes are the flop pair of
     `edge-split-operad-satisfies-ore`.
   - The rounds add 2, then 4 (sizes 6, 7, 8, 10), then 1 (size 12), then none.
   - Every pair of elements of `𝒮` has a common upper bound with at most 12 pieces.
     Every minimal one of those already lies in `𝒮`.
2. **Finite type, conditionally.** Suppose
   - **(H)** no two elements of `𝒮` have a minimal common upper bound with more than
     12 pieces.

   Then `𝒮` is the spine, so the rank-three edge-split operad has finite type. With
   Ore's condition (`edge-split-ore-iff-synchronization-and-tree-domination`: (Sync′)
   and (TD)), Thumann's theorem, as in `non-lcm-dissection-operad-groups-are-f-infinity`,
   makes `π_1(𝒪_E)` of type `F_∞`. That group contains `GL_3(Z)`, and it equals `𝒯_2`
   under saturation.
3. **Splitting categories (condition (G) of bh-invent-07), computed.**
   - The flop classes have 6 elements in 2 components, the machine version of
     bh-major-mcg-2's hand result.
   - Every other class has a **connected** splitting category: 6, 24, 17, 63 and 315
     elements for sizes 6, 7, 8, 10 and 12.

   With finite type this is not needed. It is recorded for the higher-rank search,
   where (G) may have to replace finite type.

## Evidence for (H)

- **What (H) says.** (H) holds if and only if every nontrivial split tree `X` has a
  *greatest* element of `𝒮` below it. That is the defining property of the spine.
  - **(⇐)** If a minimal bound `M` of `S_1, S_2 ∈ 𝒮` were missing from `𝒮`, the
    greatest element of `𝒮` below `M` would be an upper bound of `S_1` and `S_2`
    below `M`. By minimality it would equal `M`, a contradiction.
  - **(⇒)** Let `G` be maximal among the elements of `𝒮` below `X`, and let `S` be
    another one. The finitely many trees `U` with `G, S ≤ U ≤ X` include `X`. A minimal
    one among them is a minimal common upper bound of `G` and `S`, so under (H) it
    lies in `𝒮`. By maximality it equals `G`, so `S ≤ G`.
- **Tests of that property.** PENDING (see the artifact):
  - all split trees with at most 7 pieces;
  - random split trees with 8 to 80 pieces;
  - reversing upper bounds with up to 400 pieces.

## Lesson for general BH

A non-LCM dissection operad can still have finite type.
- **What happens here.** The flops make minimal common refinements non-unique, but
  closing under them stops quickly. In rank three it stops at the barycentric fan and
  three larger configurations built around it.
- **Where the difficulty lies.** For the edge-split host, then, the obstacle to a
  finitely presented Thompson-like group of `GL_3(Z)` is not the size of the spine.
  It is the calculus of fractions (Sync and TD).
- **The test for higher rank.** Whether the closure also stops in rank 4 and above.
  The same bounded exact search decides it in seconds per pair, and it is the next
  computation for the closed-MCG host.
