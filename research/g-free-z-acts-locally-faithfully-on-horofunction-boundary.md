---
rg: 2
id: g-free-z-acts-locally-faithfully-on-horofunction-boundary
kind: claim
title: For every nontrivial finitely generated G, no nontrivial element of G*Z fixes a nonempty open subset of the horofunction boundary of G*Z pointwise
distinct_from:
  hyperbolic-groups-embed-in-contracting-rsgs: that imports BBMZ's embedding of G*Z into a full contracting RSG, including their faithfulness of the action on the horofunction boundary (Theorem thrm:FreeProductBoundary); this strengthens faithfulness to local faithfulness, which the undistortion argument needs.
---

**ESTABLISHED** (lane proof below, elementary, not independently reviewed).

**Setting** (BBMZ arXiv:2309.06224, Subsection `ssec:free_Z_factor`, read at source). `G` is nontrivial and
finitely generated, `G' = G * ⟨t⟩` has the generating set `S_G ∪ {t}`, and `∂_h G'` is its horofunction
boundary. For `w ∈ G'` ending in `t` (resp. `t^{-1}`), the cone `C(w)` is the set of `wh` with `h` not
beginning with `t^{-1}` (resp. `t`). By their Lemma `lem:ConesAreAtoms` (and its symmetric version stated in
the proof of `lem:atoms_in_atoms`), `C(w)` is an infinite atom of level `|w|`. `∂A` denotes the shadow of
an atom `A`.

**Statement.** If `1 ≠ w ∈ G'` and `U ⊆ ∂_h G'` is nonempty and open, then `w` moves a point of `U`.

## Proof

**Step 1: every nonempty open set contains the shadow of a cone.** Shadows of infinite atoms form a basis
(BBMZ, citing BBM Theorem 3.6), so `U ⊇ ∂A` for an infinite atom `A` of some level `n ≥ 1`. Pick `a ∈ A`
with `|a| ≥ n+1` (atoms of the tree are infinite). In the Cayley graph of `G'` every `t`-edge is a
bridge. So, exactly as in the proof of `lem:atoms_in_atoms`, `C(at) ⊆ A` if `a` does not end in `t^{-1}`,
and otherwise `C(aft) ⊆ A` for any nontrivial `f ∈ G`. Every geodesic from that cone to `B_n` passes
through `a`, so its elements are `B_n`-equivalent to `a`. That cone is an atom of level greater than `n`
contained in `A`, hence a descendant of `A`, so its shadow lies in `∂A`.

**Step 2: a tree.** Let `T` be the tree whose vertices are the cosets `xG` and whose edges are the
`t`-edges `x → xt`. This is the Bass–Serre tree of `G' = G *_{1}` (HNN with trivial edge group). `G'` acts
by left multiplication without inversions, with trivial edge stabilizers. Every vertex has degree
`2|G| ≥ 4`. For an oriented edge `e`, let `H(e)` be the set of group elements on the head side of the
corresponding bridge. If `1 ∉ H(e)`, then `H(e) = C(v)` with `v` the head of `e`, and `v` ends in `t` or
`t^{-1}`. Also `g H(e) = H(ge)`.

**Step 3: a disjoint cone moved by `w`.** Let `C(u) ⊆ A` be the cone from Step 1, so `C(u) = H(e_u)`. Call an edge `e` *deep* if `H(e) ⊆ H(e_u)` and `H(e)` misses a given finite set `Φ` of vertices. Deep edges pointing away from `Φ` exist at every distance: start at a vertex of `H(e_u)` and repeatedly leave along an edge not on a geodesic toward `Φ ∪ {tail of e_u}`. At each step at most three of the at least four edges are excluded (those toward `p` or `ℓ`, toward `1G`, and toward the tail of `e_u`), so the walk continues. Each step moves farther from all of them.
- If `w` fixes a vertex `p` of `T`, choose a deep edge `e` (with `Φ = {p, 1G}`) pointing away from `p`, with
  `d(p, e) > d(p, 1G) + 1`. Then
  `we` also points away from `p`, and `d(p, we) = d(p, e)`. Two edges pointing away from `p` at equal
  distance are equal or have disjoint half-trees, and `we ≠ e` because edge stabilizers are trivial and
  `w ≠ 1`. So `H(e) ∩ H(we) = ∅`.
- Otherwise `w` is loxodromic with axis `ℓ`. Choose a deep edge `e` pointing away from `ℓ`, with
  `d(e, ℓ) > d(1G, ℓ) + 1`. Walk as above, excluding the direction toward `ℓ`. Then `we` points away from `ℓ` at the same
  distance, and `we ≠ e`, so again `H(e) ∩ H(we) = ∅`.

In both cases `1 ∉ H(e) ∪ H(we)` by the distance choice. So `H(e) = C(v)` and `H(we) = wC(v) = C(wv)` are
disjoint cones, and `C(v) ⊆ C(u)`.

**Step 4: shadows.** For an atom `A'` of level `m`, `∂A'` is exactly the set of limits of `d̄_{x_k}` with
`x_k ∈ A'`. If `h = lim d̄_{x_k}` then `d̄_{x_k}` agrees with `h` on `B_m` for large `k`. With the action
`(g·h)(y) = h(g^{-1} y)` one has `g·d̄_x = d̄_{gx}`, so `w ∂C(v) = ∂C(wv)`. Disjoint atoms have disjoint
shadows, since a common boundary point would be a descending path of atoms through both (BBM
Theorem 3.6), forcing them to intersect. Hence `w` maps the nonempty set `∂C(v) ⊆ ∂C(u) ⊆ U` into the
disjoint set `∂C(wv)`, and so moves every point of `∂C(v)`. ∎

**Remark.** The same statement holds on `C_r` under the address homeomorphism `φ : C_r → ∂_h G'` that BBMZ
use, since local faithfulness is a topological property.
