---
rg: 2
id: cocompact-tree-end-shifts-are-quantum-rigid
kind: claim
title: The end action of any cocompact action on a locally finite tree with finitely generated vertex stabilizers is a quantum-rigid SFT over the acting group; over PSL_2(Z[1/p]) for p = 2, 3 or p ≡ 11 mod 12 it passes every ring-side gate without freeness
distinct_from:
  free-group-boundary-shifts-are-quantum-rigid: that is the case of trivial vertex stabilizers (a tree Cayley graph); this allows infinite vertex stabilizers, which the family collapses by a relabeling identity, and covers amalgams and HNN extensions over finite-index edge groups, Baumslag–Solitar groups and S-arithmetic rank-one lattices.
  free-product-fp-hosts-orient-the-bass-serre-tree: that shows the end-space host over a free product with a one-ended factor is not finitely presented (infinite valence); this is the locally finite side of the same boundary, where the end-space host is finitely presented whenever the acting group is.
  euclidean-building-boundary-shifts-are-quantum-rigid: that asks for chamber-boundary shifts in rank two and higher; this settles rank one in full generality (every cocompact tree action with finitely generated stabilizers), not only for simply transitive lattices.
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that embeds groups acting cocompactly on locally finite trees in finitely presented simple groups by permutation-group envelopes; this gives the same class quantum-rigid end SFTs, i.e. finitely presented Cantor crossed-product hosts, and so says nothing new about Boone–Higman for these groups.
  finite-permutation-cocycles-cannot-cancel-infinite-isotropy: that is a measurable statement about finite permutation holonomy over infinite stabilizers; item 5 here is its elementary topological analogue for finite-fibre factor maps.
---

**ESTABLISHED** by `cocompact-tree-end-shift-rigidity-proof` (lane swarm-0917-w11-bh-last1,
2026-09-18; elementary lane proof, not reviewed, no priority claimed), except the items marked
*recalled*. Quantum rigidity (Q1–Q3) is as in
`fp-v-times-subshift-full-groups-force-quantum-rigidity`.

## Setting

- `Λ` is a group with finite symmetric generating set `S`. It acts by automorphisms (inversions allowed)
  on an infinite locally finite tree `T` with finitely many vertex orbits.
- Orbit representatives `v_1, …, v_k`. Each stabilizer `Λ_i = Stab(v_i)` is finitely generated, by `S_i`.
- `L_i` is the finite set of edges at `v_i`. The alphabet is `A = L_1 × … × L_k`.
- **Coding.** For an end `ξ ∈ ∂T` and `h ∈ Λ`, let `x_ξ(h)_i = h^{-1}·[first edge from h v_i toward ξ]`,
  which lies in `L_i`.
- **Rules.** There are finitely many edge orbits. For each, fix a representative `ε = {c v_i, c' v_j}` with
  `c, c' ∈ Λ`. Let `ε_c = c^{-1}·ε ∈ L_i` and `ε_{c'} = c'^{-1}·ε ∈ L_j`. `X_T ⊆ A^Λ` is cut out by:
  - (R1) `x(hs)_i = s^{-1}·x(h)_i` for all `h`, all `i` and all `s ∈ S_i`;
  - (R2) for each representative `ε`, exactly one of `x(hc)_i = ε_c` and `x(hc')_j = ε_{c'}` holds.
- `D_0` is the maximum of `1`, the lengths of all `s ∈ S_i`, and the lengths of all `c, c'`.

Read `h c x(hc)_i` as "the arrow at the vertex `h c v_i`". (R1) says the arrow at a vertex does not
depend on which site codes it. (R2) says that on the edge `h·ε`, exactly one endpoint points across it.

## Statement

1. **Coding.** `X_T` is an SFT with forbidden patterns in `B_{D_0}`. The map `ξ ↦ x_ξ` is a
   `Λ`-equivariant homeomorphism `∂T → X_T`, for the shift `(λ.x)(h) = x(λ^{-1}h)`.
2. **Rigidity.** For every `D >= D_0` and every field `k`, `X_T` is `D`-quantum rigid over `k`. The proof
   uses no property of `k`.
3. **Stabilizer collapse (the new step).** Let `E^i_b(h) = Σ_{a_i = b} E_a(h)` be the coordinate marginals
   of a `D`-quantum family. Then `E^i_b(h) = E^i_{λ^{-1}b}(hλ)` for all `λ ∈ Λ_i` (proof, Step 1). So the
   family is really indexed by the vertices of `T`, whatever the size of the vertex stabilizers.
4. **Dynamics.**
   - *Topological freeness.* Suppose every vertex of `T` has degree at least 3, and no nontrivial
     element of `Λ` fixes pointwise a half-tree (the vertices beyond some edge). Then the action on
     `X_T` is topologically free. The degree bound is needed: a line with `Λ = Z` has no half-tree
     fixators, but the translations fix both ends.
   - *Residual-finiteness obstruction.* The finite residual of each `Λ_i` acts trivially on `T`. So if
     `X_T` is topologically free, every `Λ_i` is residually finite. A subgroup of `Λ` with Serre's
     property FA fixes a vertex, so it is residually finite too.
   - *Minimality* (recalled, standard). If the action is of general type (no fixed end, no invariant
     line), the end action is minimal. The reason: cocompactness makes every end conical, so `∂T` is
     the limit set.
5. **Freeness cannot come from finite fibres.** Let `ξ` be fixed by an infinite subgroup `H ≤ Λ`, for
   instance the attracting end of a hyperbolic element.
   - If `π: Z → X_T` is a factor map and `π^{-1}(x_ξ)` is finite, then `Λ` does not act freely on `Z`.
   - So no deterministic extension of `X_T` is free. Those extensions are at most `|F|`-to-one, by
     `deterministic-extensions-of-rigid-sfts-are-rigid`, item 3.
   - For `X_T` minimal, a group `Λ'` and any `Λ'`-system `Y`, no nonempty closed `Λ×Λ'`-invariant
     `W ⊆ X_T × Y` is free.
   - So freeness must come from infinite fibres over the ends fixed by hyperbolic elements.
6. **Calibration.** Let `Λ = PSL_2(Z[1/p])` act on the Bruhat–Tits tree `T_{p+1}`, with
   `∂T = P^1(Q_p)`, where `p = 2`, `p = 3` or `p ≡ 11 mod 12`.
   - `X_T` is a quantum-rigid, minimal, topologically free SFT.
   - No nontrivial element of finite order has a fixed point.
   - So `B = LC(X_T, F_2) ⋊ Λ` is finitely presented, simple with centre `F_2` (recalled: Steinberg
     algebras of minimal effective Hausdorff ample groupoids, Brown–Clark–Farthing–Sims and
     Steinberg), and `K_*(B ⊗ L) = 0`.
     The last point is conditional on Farrell–Jones for `Λ` (recalled: Rüping, S-arithmetic groups)
     via `farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts`.
   - The same holds without the congruence on `p` for any torsion-free finite-index `Γ ≤ Λ`, via
     `cantor-crossed-product-leavitt-tensors-are-k-trivial`. `Γ` is not virtually free: it meets the
     upper-triangular `Z[1/p] ⋊ Z` in a finite-index subgroup.

## Consequence for the master route (gate G2)

Every ring-side gate of `research/artifacts/gq-bh-synthesis-master-route.md` passes, over an explicit
non-virtually-free group with torsion, without freeness:
- (E), finite presentation;
- central simplicity;
- (K), vanishing K-theory, where finite subgroups acting freely suffice.

So G2 may be weakened to **G2′: a quantum-rigid, minimal, topologically free SFT on which every
finite-order element is fixed-point free.** Item 5 then says where the remaining difficulty sits.
- Over torsion-free hosts G2′ is just "rigid, minimal and topologically free". Items 2 and 4 supply it,
  with no freeness, over every torsion-free group acting cocompactly and of general type on a locally
  finite tree of minimal degree at least 3 with finitely generated stabilizers and no half-tree
  fixators.
- It does not supply G2′ over the master route's `Λ_0 × H` with `Λ_0 ⊇ G`. There `Λ_0` needs its own
  effective rigid system. By item 4, no tree-end host provides one when `G` has property FA and is not
  residually finite.
- What G2′ does not supply is the *input*: hard languages (Attempt 6 of
  `decidable-group-algebras-have-fp-cantor-crossed-hosts`) and the embedding of `G`. The tree part
  carries none. Each `Λ_i` acts on `∂T` through its closure in `Aut(T)`, which is profinite.

## Examples covered by item 2

- Amalgams `A *_C B` and HNN extensions `A *_C` in which `C` has finite index in the vertex groups and
  the vertex groups are finitely generated.
- `BS(m, n)`.
- `SL_2(Z[1/p])` and `PSL_2(Z[1/p])`, with vertex stabilizers conjugate to `SL_2(Z)` or `PSL_2(Z)`.
- Uniform tree lattices (finite vertex stabilizers), including the free-group case.
- Products of any of these with rigid SFTs over other groups, via `quantum-rigidity-is-product-stable`.
