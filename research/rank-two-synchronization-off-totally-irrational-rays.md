---
rg: 2
id: rank-two-synchronization-off-totally-irrational-rays
kind: claim
title: In rank two, nested unimodular cells sharing a ray are edge-split descendants, so synchronization holds except possibly at totally irrational directions
distinct_from:
  unimodular-cells-synchronize-under-edge-splits: that is the full synchronization statement Sync_m; this proves it for m = 2 at every point of the rational Cantorization over a ray that lies on a rational plane, and reduces the rest to a shared-vertex problem at totally irrational rays.
  edge-split-descendants-are-not-factor-closed: that shows a descendant lying in a child need not descend from it; this shows the failure needs the two cells to share no ray (for m = 2).
---

**ESTABLISHED** (lane bh-free-61, 2026-09-18). Lane proof, elementary, not
independently reviewed. No priority claimed.

## Setting

Notation of `edge-splits-cut-every-rational-hyperplane` and
`unimodular-cells-synchronize-under-edge-splits`.
- `Desc(C)` is the set of iterated edge-split descendants of a unimodular cell `C`.
- A ray `ξ` is *totally irrational* if it lies on no rational plane.
- For a ray `g` of a cell, the *link* at `g` is the lattice `Z^{m+1}/Zg`. The
  *corner* of a cell `cone(g, a, …)` at `g` is `cone(ā, …)` in the link.

## Statement

1. **Facet lemma** (any `m`). Let `c' ⊆ f` be unimodular cells that share all rays
   but one. Then `c' ∈ Desc(f)`.
2. **Vertex lemma** (`m = 2`). Let `c' ⊆ f` be unimodular cells that share one ray
   `g`. Then `c' ∈ Desc(f)`.
3. **Rational points** (`m = 2`). Let `c ⊆ F` be unimodular cells. Then every
   point of the clopen `c ⊆ Ŝ_2` lying over a rational ray lies in a common
   descendant of `c` and `F`.
   - For general `m`, the same holds at such a point `x` whenever local
     synchronization holds in `Ŝ_{m−1}` at the link point of `x`. So these
     points reduce to one dimension lower.
4. **Rational planes** (`m = 2`). The same holds at every point over an irrational
   ray that lies on a rational plane.
5. **Reduction.** `(Sync_2)` holds for `c ⊆ F` if and only if, for every totally
   irrational ray `ξ` in the interior of `c`, some cell of `Desc(c)` and some cell
   of `Desc(F)`, both containing `ξ`, share a ray.

## Proofs

**1.** Write `c' = cone(a_1, …, a_m, t)` and `f = cone(a_1, …, a_m, t')`.
- Both `t̄` and `t̄'` generate `Z^{m+1}/⟨a_i⟩ ≅ Z` on the same side. So
  `t = t' + Σ x_i a_i` with `x_i ∈ Z`, and `x_i ≥ 0` because `t ∈ f`.
- Split `f` along `(a_1, t')`, keeping the child that replaces `t'` by
  `t' + a_1`. Do this `x_1` times, then continue with `a_2` and so on. The result
  is `c'`.

**2.** Write `f = cone(g, a', b')` and `c' = cone(g, a, b)`.
- The corners `L_{c'} ⊆ L_f` are unimodular cones in the rank-two link.
- A unimodular subcone of a unimodular plane cone is a Stern–Brocot descendant of
  it, since `SL_2(Z) ∩ Mat_2(Z_{≥0})` is free on the two elementary matrices.
- Splitting `f` along `(a', b')` performs a Stern–Brocot step on the corner. The
  splitting plane contains `g`, and the corner of `c'` lies on one side of it, so
  `c'` stays inside the chosen child.
- After finitely many steps, `f` has become `f'' = cone(g, a'', b'') ⊇ c'` with
  corner `L_{c'}`. Then `ā = ā''`, so `a = a'' + xg` with `x ∈ Z`. Since `a ∈ f''`
  and link coordinates are unique, `x ≥ 0`. Likewise `b = b'' + yg` with `y ≥ 0`.
- Split `x` times along `(g, a'')`, keeping the child that replaces `a''` by
  `a'' + g`, then `y` times along `(g, b'')`. The result is `c'`.

**3.** Let `x ∈ c` lie over the rational ray `v`.
- **Cells with vertex `v`.** Cut `c` by `m` independent rational planes through
  `v`, using the cut lemma. The piece containing `x` has `v` in its closure and
  lies in a pointed sector with apex `v`, so `v` is one of its rays. Call it
  `c'`. In the same way, get `f' ∈ Desc(F)` with ray `v` and `x ∈ f'`.
- **A common link cell.** In the link at `v`, the corners of `c'` and `f'` both
  contain the link point `x̄` of `x`. For `m = 2` the link has rank one, and the
  one-dimensional cut lemma gives a unimodular link cone `λ = cone(p̄, q̄) ∋ x̄`
  inside both corners.
- **Lifting.** Lift `p̄, q̄` to `p = p_0 + sv` and `q = q_0 + s'v`. For `s, s'`
  large, `p, q ∈ c' ∩ f'`. Then `cone(v, p, q)` is unimodular, contains `x`, and
  lies in both `c'` and `f'` with the shared ray `v`. By part 2 it lies in
  `Desc(c') ∩ Desc(f') ⊆ Desc(c) ∩ Desc(F)`.
- **General `m`.** Replace the one-dimensional step by a common link descendant
  `λ ∋ x̄`, which is exactly local synchronization in `Ŝ_{m−1}`. Link
  descendants of a corner come from splitting `c'` along pairs of rays other than
  `v`. Match the lifts by splitting along `(v, ·)`, which only raises lifts.

**4.** Let `ξ` be irrational on the rational plane `Π`, and `x` a point over `ξ`
on the side `+`.
- Cut `c` by `Π`. The piece containing `x` is a cell `c'` on side `+`. Its face in
  `Π` contains `ξ`, which is not rational, so that face is an edge
  `[a, b] ⊂ Π` with `ξ` in its relative interior. Get `f' ∈ Desc(F)` in the same
  way.
- In the rank-two lattice `Π ∩ Z^3`, Serret's theorem (every unimodular subcone
  is a Stern–Brocot descendant, and Stern–Brocot cells around an irrational ray
  shrink to it) gives a common Stern–Brocot descendant `[α, β] ∋ ξ` of both
  edges. Splitting along the edge pair realizes these steps on `c'` and on `f'`.
  This gives `cone(α, β, t) ∈ Desc(c')` and `cone(α, β, t') ∈ Desc(f')`, both
  containing `x`.
- `t − t' ∈ Π ∩ Z^3 = ⟨α, β⟩`, so `t'' = t + Nα + Nβ` lies in both cells for
  large `N`. The cell `cone(α, β, t'')` contains `x`, and by part 1 it lies in
  both descendant sets.

**5.** By the local form of `unimodular-cells-synchronize-under-edge-splits`,
`(Sync_2)` for `c ⊆ F` is local synchronization at every point of `c ⊆ Ŝ_2`.
Parts 3 and 4 cover every point except those over totally irrational rays, and
over such a ray there is exactly one point.
- **(⇒)** Any ray of a common descendant containing `ξ` is shared.
- **(⇐)** Let `c_1 ∈ Desc(c)` and `f_1 ∈ Desc(F)` both contain `ξ` and share the
  ray `g`. Then `Q = c_1 ∩ f_1` is a convex cone with extreme ray `g`, and `ξ` is
  interior to it.
  - Take Stern–Brocot link cells `λ = cone(p̄, q̄) ∋ ξ̄` inside both corners,
    shrinking to `ξ̄`.
  - Take `p` and `q` to be the least lifts lying in `Q`. Each least lift is within
    one step `g` of where its line leaves `Q`. That step has projective length of
    order `|g|/|p| → 0`.
  - So `p̂` and `q̂` converge to the point `ẑ` where the ray from `ĝ` through `ξ̂`
    leaves `Q̂`, which lies strictly beyond `ξ̂`. For deep `λ`, `ξ ∈ cone(g, p, q) ⊆ Q`.
  - By part 2 this cell lies in `Desc(c_1) ∩ Desc(f_1)`.

## Remarks

- **The totally irrational case is now closed.** At a totally irrational ray, the
  half-tube lemma (`half-tube-lattice-points-are-edge-split-vertices`) gives the shared
  vertex that part 5 asks for. So `(Sync_2)` holds; see
  `unimodular-cells-synchronize-under-edge-splits-proof`, which also extends parts 2–5 to
  every rank.
- The hand witnesses of `edge-split-descendants-are-not-factor-closed` fit the
  vertex lemma: those witnesses share no ray with the cell they lie in.
- The bounded search recorded in `unimodular-cells-synchronize-under-edge-splits`
  won every stuck `3×3` matrix of entry sum at most 36 (10310 up to row and
  column permutations), with split depth at most 24. This is consistent with
  `(Sync_2)`. Parts 3–5 say that any genuine loss would have to come from a
  totally irrational direction.

## Lesson for general BH

Descent in rank two is governed by shared rays. The link of a ray has rank one,
where Stern–Brocot is complete, so nested cells sharing a ray always descend.
- For `𝒯_2`, and so for the closed-MCG, Deligne and Lagrangian hosts in the
  lowest case, synchronization is automatic at every rational or rationally
  constrained direction.
- The whole combinatorial gate sits at totally irrational directions. There it
  is a Diophantine shared-vertex problem: do the vertex sets of the two descent
  systems around `ξ` meet?
- In higher rank the same lifting argument reduces rational directions to
  synchronization one dimension lower. So `(Sync_m)` is an induction on `m` whose
  only new input at each level is the totally irrational case.
