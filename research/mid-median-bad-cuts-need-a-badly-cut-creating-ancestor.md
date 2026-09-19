---
rg: 2
id: mid-median-bad-cuts-need-a-badly-cut-creating-ancestor
kind: claim
title: A median can cut a descendant badly at a vertex inside a median half only if that vertex was created as the midpoint of an edge that the median crosses in an ancestor whose third vertex has median value neither 0 nor plus or minus the edge value
distinct_from:
  some-median-is-single-cut-at-the-centroid: that settles the centroid, where all three medians meet and the link carries a root system; this treats vertices on exactly one median, where no such rigidity exists, by the creation history of the vertex.
  edge-split-descendant-dissections-have-single-cut-first-splits: that is (SC); this pins down the only local configuration that can make a median fail at a vertex strictly inside a median half.
---

**ESTABLISHED** (lane bh-major-mcg-2, 2026-09-18). Lane proof, elementary, not
independently reviewed. No priority claimed.

## Setting

- **Cell and median.** `m = 2`, `g = Δ`. `M_k = ker ℓ` is the median through `e_k` and
  `v_{ij}`, with `ℓ = x_i − x_j`.
- **The vertex.** Let `p` be a vertex of a descendant `r` with `p ∈ M_k`,
  `p ∉ {e_k, c, v_{ij}}`. The medians meet only along `Rc`, so `M_k` is the only median
  through `p`.
- **Link directions.** In the link at `p`, the two directions of `M_k` are `±u`, where
  `u` spans `ker ℓ̄` and `ℓ̄` is the form induced by `ℓ`.
- **Bad cuts.** `r` is *badly cut at `p`* if its corner at `p` contains `u` or `−u` in
  its interior with a different mediant. By
  `single-cut-is-a-mediant-condition-along-the-median`, these are exactly the
  straddlers through `p` that are not single-cut.

## Statement

- **Creation.** Follow the descent path of `r`. The vertex `p` is created once, as the
  midpoint of an edge `[x, y]` of an ancestor `A = cone(x, y, z)`, so `p = x + y`.
- **When `r` is safe.** `r` is not badly cut at `p` if any one of the following holds:
  1. `x, y ∈ M_k`, so the edge lies on the median;
  2. `z ∈ M_k`, so the median passes through the opposite vertex;
  3. `ℓ(z) = ±ℓ(x)`.
- **When `r` can be bad.** A bad cut at `p` needs `ℓ(x) = s ≠ 0`, `ℓ(y) = −s` and
  `ℓ(z) = t` with `t ∉ {0, s, −s}`. In that case `A` is itself straddled by `M_k`
  without being single-cut: `M_k` enters `A` through the midpoint `p` of `[x, y]` and
  leaves through a point of `[x, z]` or `[y, z]` that is neither a vertex nor a midpoint.

## Proof

**Corners.**
- The children of `A` have corners `cone(x̄, z̄)` and `cone(ȳ, z̄)` at `p`, with
  `ȳ = −x̄`.
- As in part 2 of `single-cut-is-a-mediant-condition-along-the-median`, later splits
  keep the corner at `p` or split it in the Stern–Brocot way. So the corner of `r` at
  `p` is a Stern–Brocot descendant of one of the two creation cones.

**Case 1.** The creation line `Rx̄` is `ker ℓ̄`. Every corner then lies in a closed
half-plane bounded by the median, so it contains neither `u` nor `−u` in its interior.

**Case 2.** `z̄ ∈ ker ℓ̄`, so both creation cones have `±u` as a boundary ray. Being
smaller than a half-plane, they do not contain the opposite direction either.

**Remaining cases.**
- Here `ℓ(x) = s ≠ 0`, `ℓ(y) = −s` and `ℓ(z) = t ≠ 0`. Say `t > 0`; the case `t < 0`
  is symmetric.
- On `cone(x̄, z̄)` the form `ℓ̄` takes the values `s, t`, both positive, so that cone
  misses `ker ℓ̄`.
- On `cone(ȳ, z̄)` it takes the values `−s, t`, so that cone contains exactly one
  direction `u_+` of `ker ℓ̄` in its interior, namely `u_+ ∝ t ȳ + s z̄`.
- Its mediant `ȳ + z̄` has value `t − s`. So `u_+` is the mediant exactly when `t = s`.
- **Case 3.** If `t = s`, the only unimodular subcone of `cone(ȳ, z̄)` containing its
  mediant in its interior is the cone itself. So no descendant corner is bad.
- **Otherwise.** The corners containing `u_+` in their interior are the Stern–Brocot
  ancestors of `u_+` in `cone(ȳ, z̄)`. Only the last of them has `u_+` as mediant, so
  the others are bad.

**The trace of `M_k` on `A`.** It is the segment from `p` to the point of `[y, z]` with
`ℓ = 0`, namely `t y + s z`, up to scaling. That point is a vertex only if `t = 0`, and a
midpoint only if `t = s`. ∎

## Consequence for (SC): the case split off the centroid

A median `M_k` fails to be a single-cut split for `D` in exactly two ways.
- **(F1)** A piece of `D` is crossed by `M_k` at no vertex of the piece: the median
  enters and leaves through edge interiors. By the criterion, such a piece is never
  single-cut. The medial line of `K` in the LD_atom set-up is an example.
- **(F2)** A piece is badly cut at a vertex `p ∈ M_k`.
  - This cannot happen at `e_k`
    (`single-cut-is-a-mediant-condition-along-the-median`).
  - At `c`, some median avoids it (`some-median-is-single-cut-at-the-centroid`).
  - At a vertex strictly inside a median half, only `M_k` passes, and this node shows
    that the piece's creating ancestor for `p` has the value pattern `(s, −s, t)` with
    `|t| ∉ {0, s}`.

So (SC) says: some median that is good at `c` has neither (F1) pieces nor (F2) pieces
inside its halves.

That signature can be read off any failing configuration logged by the MSI search
(bh-free-54, job 1328984): the vertex `p`, its creating edge, and the value `t`.

## Lesson for general BH

- **Every bad cut has a bad parent cut.** In non-LCM dissection operads, a bad
  interaction between a generator's cut and a piece is inherited from the moment the
  piece's vertex was created. It is always the child of a bad cut one level up, and is
  measured by one integer ratio `t/s`.
- **The ratio `t/s`.** When it is `0` or `±1`, the cut is clean for every descendant.
  So a proof of (SC) must show that a dissection cannot need such a badly-cut ancestor
  on every median that is clean at the centroid.
