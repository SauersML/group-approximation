---
rg: 2
id: single-cut-is-a-mediant-condition-along-the-median
kind: claim
title: In rank three a median of a cell cuts a straddling descendant along one of its first splits exactly when it enters the piece at a vertex whose corner has the median's direction as mediant; at the cell's own vertices this is automatic
distinct_from:
  edge-split-descendant-dissections-have-single-cut-first-splits: that conjectures a single-cut first split exists for every descendant dissection (SC); this proves the local criterion for single cuts and settles it at the vertices of the cell and at the centroid, reducing SC to a Stern–Brocot condition at the vertices lying on one median.
  rank-two-synchronization-off-totally-irrational-rays: that uses corners at shared rays to prove descent; this uses corners at vertices on a median to decide how the median cuts a piece.
---

**ESTABLISHED** (lane bh-major-mcg-2, 2026-09-18). Lane proof, elementary, not
independently reviewed. No priority claimed.

## Setting

- `m = 2`. `g = cone(w_0, w_1, w_2)` is a cell, and a *median* of `g` is the plane
  `Π_{ij}` of its first split at the edge `(w_i, w_j)`. It passes through `w_k` and
  `w_i + w_j`.
- `ℓ` is a primitive integral form with `Π = ker ℓ`. A cell `r` *straddles* `Π` if `ℓ`
  takes both signs on the rays of `r`.
- `r` is *single-cut* by `Π` if `Π ∩ r` is a first-split plane of `r`.
- The *link* at a ray `p` is the rank-two lattice `Z^3/Zp`. The *corner* of `r` at a
  ray `p` is the cone spanned by the images of its other two rays.

## Statement

1. **Criterion.** Let `r = cone(x_1, x_2, x_3)` straddle `Π`.
   - `r` is single-cut if and only if, after reordering, `ℓ(x_3) = 0` and
     `ℓ(x_1 + x_2) = 0`.
   - Equivalently, `Π` contains a ray `p = x_3` of `r`, and the image of `Π` in the
     link at `p` is the ray through the mediant `x̄_1 + x̄_2` of the corner of `r`
     at `p`.
   - In particular, a straddler with no ray on `Π` is never single-cut.
2. **The cell's vertices.** Let `r ∈ Desc(g)` have `w_k` as a ray and straddle the
   median `Π_{ij}`. Then `r` is single-cut by `Π_{ij}`.
3. **The centroid.** The point `w_0 + w_1 + w_2` lies in the interior of no cell of
   `Desc(g)` other than `g`. So in a descendant dissection of `g`, it is a vertex of the
   dissection or lies on an edge.

## Proof

1. **The values.** The straddling values `ℓ(x_i)` are integers of both signs. A
   first-split plane of `r` passes through one ray and through the sum of the other
   two, and a rational plane through the origin meets `r` in a first-split plane
   exactly in that case. The link form follows because `Π ⊇ Rp`. So
   `ℓ(x_1 + x_2) = 0` if and only if `x̄_1 + x̄_2` lies on `Π/Rp`. That line meets the
   interior of the corner in exactly one ray.
2. **Corners at `w_k` are Stern–Brocot descendants.** Follow the descent path from `g`
   to `r`. Since `w_k` is a ray of `r`, no step replaced `w_k`. Each step is of one of
   two kinds:
   - a split at the edge `(w_k, a)`, keeping the child `cone(w_k, w_k + a, ·)`, which
     leaves the corner at `w_k` unchanged;
   - a split at the edge `(a, b)`, which performs a Stern–Brocot split `ā, ā + b̄, b̄`
     of the corner.

   So the corner of `r` at `w_k` is a Stern–Brocot descendant of `cone(w̄_i, w̄_j)`.
   - The median's direction at `w_k` is `w̄_i + w̄_j`, the mediant of that root corner.
   - Every proper Stern–Brocot descendant lies on one side of the root mediant.
   - `r` straddles, so its corner contains that direction in its interior. Hence the
     corner is the root corner and the direction is its mediant.
   - By 1, `r` is single-cut.
3. **Every child sees the centroid on its boundary.** Every child of `g` lies on one
   side of a median, and every median contains `w_0 + w_1 + w_2`. A proper descendant
   lies in a child. ∎

## Consequence for (SC)

Fix a median `Π` of the current cell, with segment from `w_k` to `w_i + w_j`. By 1,
`Π` is a single-cut split for a descendant dissection `D` if and only if every piece
crossed by `Π`:
- has a vertex `p` on `Π`;
- has, at `p`, a corner whose mediant is the direction of `Π`.

`Π` then leaves the piece through the midpoint of the opposite edge.

By 2, the condition holds automatically at `w_k`. By 3, the centroid is a vertex of `D`
or lies on an edge.

So (SC) is a Stern–Brocot statement about the finitely many vertices of `D` lying on one
of the three medians. The obstruction to a single cut is a vertex `p` on the median whose
corner contains the median's direction in its interior but has a different mediant. At
`w_k` such a corner would be a strict Stern–Brocot ancestor, and none exists.

## Lesson for general BH

- **Single cuts are rank-two Stern–Brocot conditions.** In rank three, whether a
  generator's cut only meets pieces along their own first splits is decided at the
  vertices lying on that cut. At each, the question is whether the cut's direction in
  the link is the mediant of the corner it enters.
- **At the generator's own vertex it is automatic,** because corners there are
  Stern–Brocot descendants of the root.
- **What remains of (SC).** Only vertices in the middle of a median, such as the
  centroid and vertices created there, can spoil a single cut. That is the finite
  configuration a proof of (SC) must control.
