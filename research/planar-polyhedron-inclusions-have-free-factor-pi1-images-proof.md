---
rg: 2
id: planar-polyhedron-inclusions-have-free-factor-pi1-images-proof
kind: route
title: "Proof: pass to nested regular neighbourhoods, cut the big surface along the boundary circles of the small one, and glue the pieces back by van Kampen"
target: planar-polyhedron-inclusions-have-free-factor-pi1-images
requires: []
artifacts:
  - research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md
---

Everything is PL. Throughout, `K ⊆ L ⊆ R^2` are compact connected polyhedra
and `x_0 ∈ K`. "Surface" means a compact connected PL 2-manifold with boundary
embedded in `R^2`. By invariance of domain, the manifold interior of a surface
is its topological interior in `R^2`.

## Standard facts used

- **(F0) Planar surfaces.** Every surface `S` has the form
  `S = E_0 ∖ ⋃_{j=1}^m int E_j`. Here `E_0` is a PL disk and the `E_j` are
  pairwise disjoint PL disks in `int E_0`. The boundary circles are
  `e_j = ∂E_j`.
  - Reason: apply PL Schoenflies to the boundary circles of `S`. The outer
    circle bounds a disk containing `S`. Each other circle bounds a disk whose
    interior is a component of `R^2 ∖ S`.
  - Choose base paths in `S` from the base point to each `e_j` (`j ≥ 1`), as in
    the standard picture of a disk with `m` holes cut along `m` disjoint arcs.
    The resulting based loops `y_1, …, y_m` around the inner circles form a
    basis of `π_1(S) ≅ F_m`.
  - The outer circle, based by a suitable path, reads `y_1 y_2 ⋯ y_m`.
  - In particular a surface with exactly one boundary circle is a disk.
- **(F1) Boundary loops are primitive.** Let `S` have at least 2 boundary
  circles, so `m ≥ 1`. Then every boundary circle, based by any path and in
  either orientation, is a primitive element of `π_1(S)`.
  - Primitivity is invariant under conjugation and inversion, so it suffices
    to check one based representative of each circle.
  - The inner circles give the basis elements `y_j`.
  - The outer circle gives `y_1 ⋯ y_m`. It is primitive because
    `(y_1, …, y_{m-1}, y_1 ⋯ y_m)` is a basis, obtained by one Nielsen move.
- **(F2) Van Kampen along a circle.** Let `S_1, S_2` be surfaces with
  `S_1 ∩ S_2 = c`, a boundary circle of each. Take the base point on `c`,
  thicken by collars, and apply van Kampen. Then `π_1(S_1 ∪ S_2)` is the
  pushout of `π_1(S_1) ← π_1(c) ≅ Z → π_1(S_2)`. This is a pushout, not
  necessarily an amalgam with injective maps.
  - If `S_2` is a disk, the pushout is `π_1(S_1)/⟨⟨c⟩⟩`.
  - If `π_1(S_2) = ⟨c⟩ * B′` with `c` primitive, the pushout is
    `π_1(S_1) * B′`, with `π_1(S_1)` included as a free factor. This holds
    whatever element `c` maps to in `π_1(S_1)`, including the identity.

Base points are moved to the gluing circle by a fixed path inside the smaller
surface. This conjugates images but does not affect the free-factor property.

## Step 1: reduction to nested surfaces

1. **Common triangulation.** Choose a closed triangle `D` with `L ⊆ int D`.
   Choose a triangulation `T` of `D` in which `K` and `L` are subcomplexes.
   To get one, run the line-arrangement triangulation of A3 in
   `research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md` on the
   union of the given points, segments and triangles of `K` and of `L`.
2. **Derived neighbourhoods.** Let `T″` be the second derived subdivision.
   Put `N = N(K; T″)` and `N′ = N(L; T″)`, the unions of closed simplices of
   `T″` meeting `K` and `L` respectively.
   - These are regular neighbourhoods: surfaces with `K ⊆ int N` and
     `L ⊆ int N′`, and `N` collapses to `K` and `N′` to `L` (Rourke–Sanderson,
     Ch. 3).
   - They are connected because `K` and `L` are.
   - `N ⊆ N′` because `K ⊆ L`, so `int N ⊆ int N′`.
   - `N` may touch `∂N′`, where `K` and `L` agree locally. That is why the next
     step is needed.
3. **Shrink by a collar.** Take a collar of `∂N` in `N` that is disjoint from
   `K`, and let `M` be `N` minus the open collar.
   - `M` is a surface with `K ⊆ M ⊆ int N ⊆ int N′`.
   - The inclusion `M ↪ N` is a homotopy equivalence.
4. **Homotopy equivalences.** `K ↪ N` and `M ↪ N` are homotopy equivalences,
   so by two-out-of-three `K ↪ M` is one. `L ↪ N′` is a homotopy equivalence.
5. **Transport.** The square of inclusions `K ⊆ L`, `M ⊆ N′` commutes, and its
   vertical maps `π_1(K) → π_1(M)` and `π_1(L) → π_1(N′)` are isomorphisms. It
   therefore suffices to prove:

**Surface lemma.** If `M ⊆ int M′` are surfaces and `x_0 ∈ M`, then the image
of `π_1(M, x_0) → π_1(M′, x_0)` is a free factor.

## Step 2: cutting `M′` along `∂M`

- **Setup.** By F0 write `M = D_0 ∖ ⋃_{i=1}^k int D_i`, with `c_i = ∂D_i`. By
  F0, `π_1(M)` is free on loops `x_1, …, x_k` around `c_1, …, c_k`. All `c_i`
  lie in `M ⊆ int M′`.
- **The pieces.** Put `Q = M′ ∖ int D_0` and `P_i = M′ ∩ D_i` for
  `1 ≤ i ≤ k`.
- **How they fit together.** Since `D_0 = M ∪ ⋃ D_i`:
  - `M′ = M ∪ Q ∪ ⋃_i P_i`;
  - `M ∩ Q = c_0` and `M ∩ P_i = c_i`;
  - `Q, P_1, …, P_k` are pairwise disjoint: `Q` lies outside `int D_0`, and the
    `D_i` are disjoint disks in `int D_0`.
- **The pieces are surfaces.** Each `c_i` is a PL circle in `int M′`, so near
  `c_i` the piece on each side is a half-collar. Hence `Q` and each `P_i` is a
  compact PL 2-manifold with its gluing circle as one boundary circle.
- **The pieces are connected.** Let `C` be a component of `Q` that misses
  `c_0`.
  - Components of a compact manifold are finitely many and closed.
  - `C` is disjoint from `M` (since `C ∩ M ⊆ Q ∩ M = c_0`), from the `P_i` and
    from the other components of `Q`.
  - So `C` is clopen in `M′`. It is nonempty and misses `M ≠ ∅`, which
    contradicts connectedness of `M′`.
  - Hence every component of `Q` meets the connected circle `c_0`, so `Q` is
    connected. The same argument applies to each `P_i`.
- **`Q` is not a disk.** Suppose `c_0` were the only boundary circle of `Q`.
  - Then `Q ∪ D_0` would be a compact 2-manifold without boundary, since near
    `c_0` the set `Q` is the outer half-collar and `D_0` the inner one.
  - By invariance of domain it would be open in `R^2`. It is also compact and
    nonempty, which is impossible in the connected, noncompact `R^2`.
  - So `Q` has at least 2 boundary circles, and by F1,
    `π_1(Q) = ⟨c_0⟩ * B′_Q`.
- **Each `P_i` is a disk or has primitive `c_i`.** If `c_i` is the only
  boundary circle of `P_i`, then `P_i` is a disk by F0. It is bounded by `c_i`
  and contained in `D_i`, so `P_i = D_i`. Otherwise, by F1,
  `π_1(P_i) = ⟨c_i⟩ * B′_i`.

## Step 3: gluing back

Let `Dk = {i : P_i = D_i}`. Glue the pieces to `M` one circle at a time. At
each stage the union is a surface and the next piece meets it in exactly one
boundary circle, so F2 applies.

1. **Disk pieces.** Glue `P_i` for `i ∈ Dk`. By F2 each step kills the basis
   element `x_i`, and the image of `π_1(M)` stays everything. The result is
   `F(x_1, …, x_k)/⟨⟨x_i : i ∈ Dk⟩⟩ = F(x_j : j ∉ Dk)`, freely generated by the
   images of the remaining basis elements.
2. **Non-disk inner pieces.** Glue `P_i` for `i ∉ Dk`. By F2 each step adds a
   free factor `B′_i` and includes the previous group as a free factor.
3. **The outer piece.** Glue `Q` along `c_0`. By F2 this adds the free factor
   `B′_Q`, whatever `c_0` maps to.

The result is

`π_1(M′) = F(x_j : j ∉ Dk) * (∗_{i ∉ Dk} B′_i) * B′_Q`,

and the image of `π_1(M)` is exactly the first factor. This proves the surface
lemma, and by Step 1 the claim.

The case `k = 0` is included: `M` is a disk and the image is trivial.

## Why the algebraic obstruction does not bite

- The "kill then include" composites of
  `research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md` §6 can
  produce non-free-factor images such as `x_1^2`.
- Here the argument never composes such steps abstractly. The kills come only
  from disks that fill holes of `M` itself, and they kill basis elements of
  `π_1(M)`. Every other piece is attached along a primitive circle, which only
  adds a free factor.
- Planarity enters twice:
  - through F0/F1, the structure of planar surfaces;
  - through "Q is not a disk", which fails on the sphere.
- On a torus, or on any non-planar surface, the argument breaks: a boundary
  circle can bound a once-punctured torus, whose boundary loop is a commutator
  and not primitive.
