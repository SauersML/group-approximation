---
rg: 2
id: hyperbolic-free-product-contracting-rsg-proof
kind: route
title: Shadows of points just past a syllable change are atoms of one type, and translating a factor branch into such a shadow copies every atom type, so the type graph of A * B has an irreducible core
target: free-products-of-hyperbolic-groups-are-contracting-rsgs
requires:
  - hyperbolic-groups-embed-in-contracting-rsgs
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

Lane `bh-free-23`, 2026-09-18. Lane proof, not reviewed. BBMZ arXiv:2309.06224v3, TeX
`gq/src/bh-free-03/bbmz2-2309.06224.tex`; the labels below are TeX labels.

**Geometry.**
- **Setting.** `K = A * B`, `S = S_A ∪ S_B`. The Cayley graph is a tree of copies of `Cay(A)`
  and `Cay(B)` glued at single vertices. Word length adds over syllables.
- **Branches.** For a vertex `v`, the *A-branch* `D^A_v` is `v` together with everything
  reached from `v` through the `A`-coset `vA` without returning to `v`; the *B-branch* `D^B_v`
  is defined similarly. If the normal form of `v` ends in a `B`-syllable (or `v = 1`), then
  `D^A_v = {vh : h = 1 or h starts with an A-syllable}` and `|vh| = |v| + |h|`.
- **Cut vertices.** `v` separates each of its branches from the rest of the graph.
- **Shadows.** For `n = |q|`, write `Sh(q)` for the atom of `B_n` containing `q`. It equals
  `{x : d(x,p) = d(x,q) + d(q,p) for all p ∈ B_n}`, the points gated through `q`.

**Step 1 (a universal type).**
- **The words.** Fix `b ∈ S_B^{±1}`. Let `𝒬_b` be the set of words `q = y b` with `y` ending
  in an `A`-syllable and `|q| = |y| + 1`.
- **The shadow is local.** For `q ∈ 𝒬_b`, `y` is a cut vertex. For points of `D^B_y`, being
  gated through `q` with respect to `B_{|q|}` is the same as being gated through `q` with
  respect to `yB ∩ B_{|q|} = y·(S_B ∪ {1})`. So `Sh(q)` consists of:
  - the `B`-coset points `yβ` whose `Cay(B)`-geodesics to the radius-1 ball pass through `b`;
  - `D^A_q`;
  - the `A`-branches at those `yβ`.

  This set is infinite. It depends only on `b` and on the geometry of `Cay(B)`.
- **One type.** For `q, q' ∈ 𝒬_b`, left multiplication by `y'y^{-1}` maps `D^B_y` isometrically
  onto `D^B_{y'}` and shifts lengths by `|y'| − |y|`. It maps `Sh(q)` onto `Sh(q')`. Atoms
  inside these branches are determined by profiles on the branch, since the outside is reached
  through `y`. So `y'y^{-1}` maps descendant atoms to descendant atoms and is a morphism
  (`def:morphisms`). All `Sh(q)`, `q ∈ 𝒬_b`, have one type `τ_b`.
- **The mirror type.** Symmetrically, fix `a ∈ S_A^{±1}`. The shadows `Sh(q')` for `q' = y'a`,
  with `y'` ending in a `B`-syllable, have one type `τ'_a`.

**Step 2 (every infinite atom contains τ_b or τ'_a).**
- **Setup.** Let `𝔄 ∈ 𝒜_n(K)` with `n ≥ 1`, and pick `x ∈ 𝔄` with `|x| > n`.
- **`x` ends in a B-syllable.** Pick `a_1 ∈ A \ {1}`, so `x a_1` ends in `A`, and put
  `q = x a_1 b ∈ 𝒬_b`.
  - `D^A_x ∩ B_n = ∅`, and `x` is a cut vertex, so every point of `D^A_x` has the profile of
    `x` on `B_n`. Hence `D^A_x ⊆ 𝔄`.
  - `Sh(q)` lies in the `B`-branch at `x a_1`, which lies in `D^A_x`. So `Sh(q) ⊆ 𝔄`, and it is
    a descendant atom (its level `|q|` exceeds `n`) of type `τ_b`.
- **`x` ends in an A-syllable.** The mirror argument gives a descendant of type `τ'_a`.
- **The two types reach each other.** `Sh(q)` contains `D^A_q`, which contains
  `z = q a_2 b_2 a` with `q a_2 b_2` ending in `B`. And `Sh(z) ⊆ D^A_q` has type `τ'_a`.
  Symmetrically, `τ'_a` reaches `τ_b`.

**Step 3 (τ_b reaches every non-root type).** Every atom of level `≥ 1` lies in `D^A_1` or in
`D^B_1`. In `D^A_1`, the neighbor of `1` on a geodesic lies in `S_A^{±1}`, which the `B_1`-profile
detects. Take an atom `A'` of level `n ≥ 1` inside `D^A_1`, and `q ∈ 𝒬_b`.
- **The translate lies in one atom.** `q` maps `D^A_1` isometrically onto `D^A_q ⊆ Sh(q)` with
  `q(D^A_1 ∩ B_n) = D^A_q ∩ B_{n+|q|}`. Geodesics from `D^A_q` to its complement pass through
  `q`. So for `a' ∈ A'`, the profile of `qa'` on `B_{n+|q|}` is `d(a', q^{-1}·)` on `D^A_q`,
  and `|a'| + d(q,·)` off it. So `qA'` lies in one atom `A''`.
- **That atom is exactly `qA'`.**
  - Every `B`-neighbor `v` of `q` lies in `B_{n+|q|}`. For points of `D^A_q`,
    `d(·,v) = d(·,q) + 1`.
  - Every other point `x ≠ q` reaches `q` through some `B`-neighbor `v`, so there
    `d(x,v) = d(x,q) − 1`.

  So `A'' ⊆ D^A_q ∪ {q}`, and `q^{-1}A''` has the profile of `A'` on `B_n`; off `D^A_1`, paths
  go through `1`. Hence `A'' = qA'`.
- **Conclusion.** The same holds for descendants, so `q` is a morphism `A' → qA'`, a descendant
  of the `τ_b`-atom `Sh(q)`. This is BBMZ `lem:atoms_in_atoms` with `t` replaced by `q`.
- **The other side.** Atoms in `D^B_1` are copied the same way into `τ'_a`-atoms, and `τ_b`
  reaches `τ'_a`.

**Step 4 (conclusions).**
1. *No isolated points.* Every atom contains a `τ_b`- or `τ'_a`-atom. A `τ_b`-atom `Sh(q)`
   contains two disjoint infinite atoms:
   - `Sh(q a_1 b)` and `Sh(q a_2 b)`, in the disjoint branches `D^B_{q a_1}` and `D^B_{q a_2}`,
     with `a_1 ≠ a_2` in `A \ {1}`, if `|A| ≥ 3`;
   - otherwise `Sh(q a b_1)` and `Sh(q a b_2)`, distinct atoms of one level, with `b_1 ≠ b_2`
     in `S_B^{±1}`. This needs `|B| ≥ 3`.

   The hypothesis `(|A|,|B|) ≠ (2,2)` guarantees one of the two.
2. *Faithfulness.* `A * B` has no nontrivial finite normal subgroup: such a subgroup is
   conjugate into a factor, and conjugation by the other factor moves it off. `A * B` is
   non-elementary hyperbolic, so the action on `∂_h` is faithful (`rmk:horofunction_problems`,
   via Webster--Winchester).
3. *Irreducible core.* By Steps 2–3, every node reaches `τ_b`, and `τ_b` reaches every non-root
   node. The root is included if its type recurs. So `Γ_0`, the set of nodes reachable from
   `τ_b`, is strongly connected. It is not a single cycle, by (1). Only the root can lie outside
   `Γ_0`, and then it has no incoming edges. These are conditions (i)–(iii) of the definition.
4. *Contracting RSG.*
   - `K` is hyperbolic, so it has finitely many atom types (`prop:fin_many_types`).
   - Its action is rational (`thrm:BBM`, using (1)), and the image is an RSG
     (`prop:hyp_similarities`).
   - The image has finite nucleus (`thrm:contracting`).
   - With (3), it is contracting (`def:contracting`), and by (2) it is isomorphic to `K`. ∎

**Calibration.** For `B = Z = ⟨t⟩`, `S_B = {t}`, the shadow `Sh(q)` with `q` ending in `t` is
BBMZ's `C(w) = {wh : h does not begin with t^{-1}}`, and the argument reduces to theirs. For
`B` finite with `S_B = B \ {1}`, the `B`-cosets are cliques, `Sh(q) = D^A_q`, and one recovers
`free-product-finite-factor-contracting-rsg-proof`.
