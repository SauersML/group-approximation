---
rg: 2
id: thompson-f-two-transitive-disagreement-sets-are-self-similar
kind: claim
title: In a 2-transitive action of Thompson's group F, the disagreement set of a pair is a perfect disconnected compact subset of (0,1) that is a translate of each of its clopen pieces
distinct_from:
  thompson-f-two-transitive-hull-endpoints-are-separated: that claim studies only the two extreme points xi < eta of a pair; this claim studies the whole closed set of points where the pair cannot be matched by an element that is the identity nearby, whose extreme points are xi and eta
  thompson-f-two-transitive-rigid-stabilizers-fix-no-point: that claim attaches a closed set to one point of the abstract set and uses its extreme point; this claim attaches a closed set to a pair of points and uses its connectivity and components
  thompson-f-two-transitive-dyadic-branching-is-binary: that claim is a local statement at one dyadic point; this claim is global on (0,1) and does not distinguish kinds 1 and 2
---

Let `F` act on a set `Ω`, `|Ω| ≥ 3`, transitively on ordered pairs of distinct
points. For `x ∈ [0,1]` let `G_x` be the group of elements of `F` that are the
identity on some neighbourhood of `x` in `[0,1]`. For `ω, ω' ∈ Ω` put

`D(ω,ω') = { x ∈ [0,1] : ω' ∉ G_x ω }`,

the **disagreement set** of the pair. Then:

1. (Basic rules.) `D(ω,ω')` is closed, `D(ω,ω') = D(ω',ω)`,
   `D(gω,gω') = g D(ω,ω')` for `g ∈ F`, and `D(ω,ω') = ∅` iff `ω = ω'`.
   For any `ω_1, ω_2, ω_3`, every point of
   `D(ω_1,ω_2) ∪ D(ω_2,ω_3) ∪ D(ω_1,ω_3)` lies in at least two of the three
   sets.
2. (One orbit.) All disagreement sets of distinct pairs form one `F`-orbit of
   closed sets. Call a representative `D_0`. It is a compact subset of `(0,1)`.
3. (Splicing.) If `x ∉ D(ω,ω')`, there is `α ∈ Ω` with
   `D(ω,α) = D(ω,ω') ∩ [0,x)` and `D(α,ω') = D(ω,ω') ∩ (x,1]`. More generally,
   every relatively clopen subset `A` of `D(ω,ω')` equals `D(ω,β)` for some
   `β`.
4. (Self-similarity.) Every nonempty relatively clopen subset of `D_0` is
   `g D_0` for some `g ∈ F`.
5. (Not connected.) `D_0` is not connected. In particular no disagreement set
   is an interval.
6. (Shape.) `D_0` has infinitely many connected components and no isolated
   points, i.e. it is a perfect set. None of its nondegenerate components (if
   there are any) is relatively open in `D_0`.
7. (Extreme points.) `max D(ω,ω') = η(ω,ω')` and `min D(ω,ω') = ξ(ω,ω')`, the
   hull endpoints as defined in
   `thompson-f-two-transitive-hull-endpoints-are-rational`. Only the
   definitions are used, not the results of that claim.

**What this kills.** Every candidate 2-transitive action in which some pair of
points has a disagreement set with finitely many components: a finite set, a
finite union of intervals and points, or a single interval. Point stabilizers
cannot be matched by local modifications on a set whose shape is finite. This
contains, with a different invariant, the counting kills of the finite-difference
and finite-interval-union affine models recorded under
`thompson-f-has-no-faithful-2-transitive-action` (2026-09-17). It does not need
the affine-model reduction, and it treats kind 1 and kind 2 of
`thompson-f-two-transitive-dyadic-branching-is-binary` together. The step where
all these models die is item 5 or item 6: disjoint disagreement sets of two
pairs `(ω,ω')` and `(ω,ω'')` force `D(ω',ω'')` to be their disjoint union, and
a cut at a gap of `D_0` must give an `F`-translate of `D_0`, which lowers a
finite number of components.

So a 2-transitive action of `F`, if one exists, has a disagreement set `D_0`
that is either a Cantor set (empty interior) or a perfect set with non-isolated
interval components. In both cases `D_0` is an `F`-translate of each of its
nonempty clopen pieces.

**Calibration.** For the order-preserving action of `F` on an orbit `F·p` in
`(0,1)`, which is not 2-transitive, `D(p_1,p_2) = [p_1,p_2]` is an interval.
There item 5 fails because the input of its proof, that no `F_U^c` fixes a
point, fails. Items 1, 3 and 4 hold there: cutting `[p_1,p_2]` at an
interior point `x ∉ D` is impossible, because `D` has no gaps.

Scope: proved here on 2026-09-18 by swarm agent `swarm-0917-w7-w7-z-break`.
There is no independent review, and no novelty is claimed.

**Proof:** `thompson-f-two-transitive-disagreement-sets-self-similar-proof`.
