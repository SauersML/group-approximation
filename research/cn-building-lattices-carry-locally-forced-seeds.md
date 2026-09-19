---
rg: 2
id: cn-building-lattices-carry-locally-forced-seeds
kind: claim
title: Every torsion-free type-preserving cocompact lattice in a thick locally finite C̃_n building (n ≥ 2) carries a locally forced finite-type seed; labels are singular subspaces S of one polar factor of the link, outward labels are T ∩ S^⊥ (one-or-all axiom), and seed rigidity reduces to a perfect boundary SFT
---

**ESTABLISHED** (lane proof, bh-invent-13, 2026-09-18; elementary building geometry; not reviewed).
- Items 1–4 are proved.
- For `n = 2` this is `c2-building-lattices-carry-finite-type-seeds`, written there in coordinates rotated by 45°.
- Rigidity of the reduced boundary is OPEN.

## Setting

**Building and lattice.** `Δ` is a thick, locally finite `C̃_n` building (`n ≥ 2`). `Γ` is a torsion-free, type-preserving,
cocompact lattice, so it acts freely on the vertex set `V`, with finitely many orbits. Examples are torsion-free
cocompact lattices in `Sp_{2n}(F)` for a local field `F`, which are Kazhdan, Helly (CCGHO Thm 1.1(4)) and not
hyperbolic.

**Apartment model.**
- The vertex set is `(½Z)^n`. The *type* of a vertex is the number of half-integral coordinates. Types 0 and `n` are
  special.
- A type-`k` vertex `x` has half-integral coordinate set `H` (`|H| = k`) and integral set `Z`.
- `Lk(x)` is the join of two polar spaces: the `C_k` space `P_H` on `H` and the `C_{n−k}` space `P_Z` on `Z`.
- Its vertices are `x + e` with `e ∈ {0, ±½}^n ∖ 0` supported in `H` (a vertex of `P_H`) or in `Z` (a vertex of `P_Z`).
  - To see this, take the alcove `{½ ≥ x_1 ≥ … ≥ x_n ≥ 0}` and apply the stabilizer `W(C_k) × W(C_{n−k})`.
  - The singular subspace of `e` is spanned by the points `q_i^{sgn e_i}`, `i ∈ supp e`.
  - `q_i^± ⊥ q_j^±` for `i ≠ j`, and `q_i^+` is not collinear with `q_i^−`.
  - Vertices of different factors are always adjacent.
- **Distance.** For a type-0 vertex `o`, `d(u, o) = 2‖u − o‖_∞` in the 1-skeleton.
  - Every edge moves each coordinate by `≤ ½`, which gives `≥`.
  - The step `e = ½ sgn(o−u)` on the set of maximal coordinates is a link vertex (those coordinates have one
    parity) and lowers `‖·‖_∞` by `½`, which gives `≤`.
- **Building distances.** Retraction onto an apartment centred at a chamber containing `o` preserves `d(·, o)`. So
  building distances are apartment distances in any apartment containing `o` and the vertices concerned.

**Origins, labels, SFT.**
- Origins range over one `Γ`-orbit `O` of type-0 vertices.
- For `o ≠ x`, put `w = o − x`, `M = ‖w‖_∞` and `I = {i : |w_i| = M}`. The coordinates in `I` have one parity, so they
  lie in one factor of `Lk(x)`, called *active* (`J = H` or `Z`). The other factor is *passive*.
- The *label* is the vertex `S = λ_o(x) := x + ½ sgn w|_I` of the active factor, a singular subspace of dimension
  `|I| − 1`. Also `λ_o(o) = *`.
- `Y` is the set of configurations whose pattern on every star equals that of some genuine field `y_o`, `o ∈ O`.

## Theorem

1. **Tables.** Let `y` be a neighbour of `x`, with subspace `T_y`.
   - `d(y,o) − d(x,o) = −1` iff `y` is active and `T_y ⊇ S`. So `In(x) = St(S)`, the set of subspaces of the active
     factor that contain `S`.
   - It is `0` iff `y` is passive, or `y` is active with `T_y ⊆ S^⊥` and `T_y ⊉ S`.
   - It is `+1` iff `y` is active with `T_y ⊄ S^⊥`.
2. **Outward labels.** For outward `y`, `λ_o(y) = T_y ∩ S^⊥` if that is nonempty, and `λ_o(y) = x` otherwise.
3. **Seed.** `(Y, *)` is an SFT compactification of `Γ` ((C1), (C2)) whose seed is **locally forced** with star
   radius.
4. **Rigidity reduction.**
   - `Y` is quantum rigid at all large scales iff `∂Y = Y ∖ Γ·y_{o_0}` is.
   - With origins all type-0 vertices, `Y_all ⊇ Y`, and the boundary `∂Y_all` is **perfect**.
   - Rigidity of `∂Y_all` implies rigidity of `Y`.

## Proof

**Tables (item 1).** Let `y = x + e`.
- *Passive `e`.* It leaves the coordinates in `I` unchanged, and each passive coordinate satisfies `|w_i| ≤ M − ½`,
  so `|w_i − e_i| ≤ M`. So the change is 0.
- *Active `e`.*
  - If `e_i = ½ sgn w_i` on all of `I`, the change is −1. The active coordinates off `I` satisfy
    `|w_i| ≤ M − 1`, and passive ones `≤ M − ½`.
  - If `e_i = −½ sgn w_i` for some `i ∈ I`, the change is +1.
  - Otherwise some `i ∈ I` has `e_i = 0`, and the change is 0.
- *In polar-space terms.* The points of `T_y` are `q_i^{sgn e_i}`. The second case says `T_y` has a point
  non-collinear with a point `q_i^{sgn w_i}` of `S`. So the three cases are `T_y ⊇ S`, `T_y ⊄ S^⊥`, and the rest.
- *In the building.* `S` lies in the convex hull of `x` and `o`: it moves each root functional `x_i`, `x_i ± x_j` by at
  most its total change towards `o`. So `S` lies in every apartment through `x`, `o` and `y`. The relations `⊇` and
  `⊥` are intrinsic to `Lk(x)`, and preimages of `St(S)` under retraction centred at a chamber through `S` are exactly
  `St(S)`.

**Outward labels (item 2).** Let `y = x + e` be outward, and `N = {i ∈ I : e_i = −½ sgn w_i}`, which is nonempty.
- Then `w' = w − e` has `M' = M + ½` and maximal set `N`. These coordinates flipped parity, so the active factor at
  `y` is the one containing `N`.
- `λ(y) = y + ½ sgn w|_N = x + e|_{supp e ∖ N}`.
- The points `q_i^{sgn e_i}`, `i ∈ supp e ∖ N`, are exactly the points of `T_y` collinear with all of `S`, so
  `λ(y) = T_y ∩ S^⊥`, or `x` if `N = supp e`.
- By the one-or-all axiom, `T_y ∩ S^⊥` is a singular subspace of `T_y` of codimension `|N|`. This is intrinsic.
- It is a face of `T_y`, so it is adjacent to `y`.
- For `n = 2` this is "the unique point of the line `y` collinear with `p`" (the GQ axiom).

**Descents (the Ã2 and C̃2 Step 3).** Write `w → w'` for `w' ∈ In(w)`.
- **Diamond.** Put `u = x + e_S`, the vertex `S` itself. Its label is `g'' = x + sgn w|_I + ½ sgn w|_P`, where
  `P` is the set of passive coordinates with `|w_i| = M − ½`.
  - For every `T ⊇ S`, write `y_T = x + e_T`. Then `g'' − y_T` has entries in `{0, ±½}`, supported on `I ∪ P ∪ supp(e_T)`.
    At `y_T` all these coordinates have one parity, so `g''` is a link vertex of `y_T`.
  - `‖w − e_T − (g'' − y_T)‖_∞ ≤ M − 1 = ‖w − e_T‖_∞ − ½`, so `y_T → g''`.
  - So all of `St(S)` descends in one step to `g''`. This is read off the star of `u`, which contains every `y_T`,
    since `T ⊇ S` makes them adjacent.
- **Sideways pairs.**
  - A passive `y`: `y → u` and `x → u` (join adjacency; the computation is the same as above).
  - An active `y` with `T_y ⊆ S^⊥`: the common descendant is `S ∨ T_y`, which is singular because `T_y ⊆ S^⊥`. It is
    exactly `λ(y)`.

**Seed (item 3).** Steps 2 and 4 of `a2-lattices-carry-finite-type-seeds` apply verbatim:
- `*` at `o_0` forces `y_{o_0}` by outward induction along geodesics;
- confluence gives one `z` below `B_R`;
- `η` agrees with the genuine `y_o`, `o ∈ O`, having the same label at `z` on `Out(z) ⊇ B_R`.

Every deduction reads one star, and the forcing closure from `o_0` is all of `V`. So the seed is locally forced in the
sense of `quantum-rigidity-is-decided-on-the-derived-subshift`.

**Rigidity (item 4).**
- *The equivalence.* By Corollary A there, `Y` is rigid iff `∂Y` is.
- *Perfectness of `∂Y_all`.* Let `η ∈ ∂Y_all`, fix `R`, and let `z` be below `B_R` with label `λ`.
  - The origins with label `λ` at `z` fill an unbounded cone.
  - At `u = λ(z)` their labels run over the vertices of `u`'s active factor opposite `z`. There are at least two, by
    thickness, and each is realized on an unbounded subcone.
  - The resulting limits `η_c ∈ ∂Y_all` all agree with `η` on `Out(z) ⊇ B_R`, since there they are determined by `λ`.
    They are pairwise distinct at `u`.
  - So `η` is not isolated.
- *Transfer to `Y`.* `Y ⊆ Y_all` over the same alphabet. Its isolated points are the locally forced seed orbits. So `Y_all` is rigid iff
  `∂Y_all` is, and a rigid `Y_all` makes its subshift `Y` rigid (`a2-lattices-carry-finite-type-seeds`, item 5). ∎

## Lesson for general BH

- The seed mechanism is uniform over polar geometry. With inward sets as labels, every label is a singular subspace
  `S` of one factor of a join of polar spaces.
- Outward propagation is the polar projection `T ↦ T ∩ S^⊥` (the one-or-all axiom), and descents close in one step
  through the join `S ∨ T`.
- So every `C̃_n` lattice, not only rank 2, has an isolated dense seed, and it is locally forced. By the
  derived-subshift theorem its rigidity is exactly rigidity of a perfect boundary SFT.
- Across Ã2 and all `C̃_n`, the higher-rank Kazhdan (IE′) problem is now purely a boundary-rigidity problem. The
  remaining building types (`Ã_n` for `n ≥ 3`, `B̃`, `D̃`, `G̃2`, `F̃4`, `Ẽ`) should follow from Tits projections in the
  same way; the same tables have to be written for each.

## Referee (bh-ref-kourovka-a, 2026-09-19): PASS for items 1–3 and for the item 4 reduction; perfectness checked in outline

I checked this against the refereed `a2-lattices-carry-finite-type-seeds` and against
`c2-building-lattices-carry-finite-type-seeds`, whose Steps 2–4 it reuses.

- **Apartment model.**
  - The alcove `½ ≥ x_1 ≥ … ≥ x_n ≥ 0` has vertex types given by the number of half-integral
    coordinates.
  - The stabilizer of a type-`k` vertex is `W(C_k) × W(C_(n−k))`: reflections in `x_i = ½` and
    `x_i ± x_j = 1` on `H`, and in `x_i = 0` and `x_i ± x_j = 0` on `Z`. Mixed walls do not pass
    through the vertex.
  - So links are joins of polar spaces of ranks `k` and `n − k`, with vertices `x + e`,
    `e ∈ {0,±½}^H` or `{0,±½}^Z`.
  - `d(u,o) = 2‖u − o‖_∞`, via the parity argument. Building distances are apartment distances, by
    retraction.
- **Item 1.**
  - The three cases (all of `I` agreeing, some sign opposite, otherwise) give `−1, +1, 0`. The active
    off-`I` coordinates are `≤ M − 1` and the passive ones `≤ M − ½`.
  - The polar translation `T ⊇ S` / `T ⊄ S^⊥` is correct, since points with index off `I` are
    collinear with all of `S`.
  - `S` lies in the convex hull of `x` and `o`: every root functional `x_i`, `x_i ± x_j` moves between
    its values at `x` and `o`, which I checked in all index cases. So labels are intrinsic.
- **Item 2.** `w' = w − e` has maximal set `N`, and `λ(y) = x + e|_(supp e ∖ N)` is the span of the
  points of `T_y` collinear with `S`, i.e. `T_y ∩ S^⊥`. It is a face of `T_y`, so it is adjacent to
  `y`. At `*`, every neighbour gets label `o`. Correct.
- **Descents.**
  - The diamond is correct. `λ(u) = x + sgn w|_I + ½ sgn w|_P` (the maximal set of `o − u` is `I ∪ P`).
    Each `y_T` (`T ⊇ S`) is adjacent to `g''` by the parity check and one step closer. This is read in
    a genuine field matching `η` on `St(u)`, which contains `x` and every `y_T`.
  - It is a **one-step** diamond, so confluence needs no termination.
  - Sideways pairs are correct:
    - for passive `y`, `u ∈ In(y)`, since `‖o − u‖ = M − ½ < ‖o − y‖ = M`;
    - for active `y` with `T_y ⊆ S^⊥`, the maximal set of `o − y` is `I ∖ supp e`, and
      `λ(y) = S ∨ T_y`.
- **Item 3.** The C̃₂ Step 4 argument transfers. In particular the matching field exists because
  `η`'s star at `z` is genuine for some `o ∈ O` **by definition of `Y`**, so the one-orbit
  restriction on origins costs nothing.
- **Item 4.**
  - `Y` rigid iff `∂Y` rigid is Corollary A, with the seed locally forced.
  - For `Y_all`, whose isolated points are exactly its locally forced seed orbits once `∂Y_all` is
    perfect, use parts 1–2 of the derived-subshift theorem. Then `Y ⊆ Y_all` gives transfer by
    subshift monotonicity. Correct.
  - Perfectness is checked **in outline only**. The limits `η_c` share `z`'s label, so they agree with
    `η` on `Out(z) ⊇ B_R`, and they differ at `u ∉ Out(z)`.
  - I verified "at least two labels at `u`, each on an unbounded family of origins" for C̃₂ at a
    special `z`. There the labels at `u` are the points of the rank-1 factor other than `z`, and there
    are `≥ 2` of them by thickness. The general case is asserted.

**Not checked:** the example claims (Helly by CCGHO Thm 1.1(4); Kazhdan), which are recalled, and the
expectation that the other building types follow.
