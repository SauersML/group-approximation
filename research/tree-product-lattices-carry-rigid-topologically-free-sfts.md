---
rg: 2
id: tree-product-lattices-carry-rigid-topologically-free-sfts
kind: claim
title: Coupled tree codings are quantum rigid, so every cocompact lattice on a product of locally finite trees carries a rigid minimal SFT coding the product of the boundaries, topologically free with torsion-free isotropy when the lattice is torsion-free; this includes the Burger–Mozes simple groups
requires:
  - locally-finite-tree-end-shifts-are-quantum-rigid-sfts
  - quantum-rigidity-is-product-stable
  - minimal-sfts-with-a-finite-modification-are-not-quantum-rigid
  - master-route-needs-only-topological-freeness
distinct_from:
  quantum-rigidity-is-product-stable: that treats products of shifts over product groups; this treats several tree codings over ONE group (a join), which is rigid exactly when the vertex stabilizers of each tree couple the others, and fails for uncoupled joins.
  torsion-free-tree-lattices-embed-in-fp-kgraph-full-groups: that proves finiteness (an F_∞ k-graph full group containing the lattice); this proves the rigidity and dynamics of the lattice's own boundary SFT, which is the (★′) half of the master route.
  locally-finite-tree-end-shifts-are-quantum-rigid-sfts: that is one tree; this is the coupled join of several, which reaches simple and non-residually-finite groups whose vertex stabilizers in each tree are virtually free.
---

**ESTABLISHED** (lane bh-star-a, 2026-09-18; elementary lane proof below, not reviewed; no priority
claimed). Notation, the rules (R1)–(R2), and quantum rigidity (Q1–Q3) are as in
`locally-finite-tree-end-shifts-are-quantum-rigid-sfts`.

## Setting

- `Λ` is finitely generated. It acts on locally finite leafless trees `T_1, …, T_k`, and each action
  satisfies the Setting of `locally-finite-tree-end-shifts-are-quantum-rigid-sfts`.
- `X_i = X_(T_i)` is the end shift of `T_i` over `Λ`.
- The **join** `X = X_1 ⋈ … ⋈ X_k ⊆ (A_1 × … × A_k)^Λ` is the set of configurations whose `i`-th
  coordinate lies in `X_i` for every `i`. It is an SFT (the union of the rules), and it is equivariantly
  `∂T_1 × … × ∂T_k` with the diagonal action.
- **Coupling (C).** For all `i ≠ j` and all vertex-orbit representatives `v` of `T_i` and `w` of `T_j`,
  `Stab_Λ(v)` has finitely many orbits on `Λ w`.

## Theorem

1. **Coupled joins are rigid.** Under (C), `X` is `D`-quantum rigid over every field for all
   `D ≥ D_1 := max(D_0(T_1), …, D_0(T_k), ⌈R/2⌉)`, where `R` is the coupling constant of the proof.
2. **Lattices.** Let `Γ ≤ Aut(T_1) × … × Aut(T_k)` be discrete and cocompact on `T_1 × … × T_k`, where each
   `T_i` is locally finite, leafless, has more than two ends, and is acted on without inversions. Then:
   - each factor action satisfies the one-tree Setting;
   - (C) holds;
   - `X` is a quantum-rigid, minimal SFT over the finitely presented group `Γ`.

   If `Γ` is torsion-free, then `X` is also topologically free with torsion-free isotropy, so `X` is a
   (★′) object in the sense of `master-route-needs-only-topological-freeness`.
3. **Uncoupled joins are not rigid.** Let `F_2` act diagonally on `T × T`, where `T` is its Cayley tree.
   (C) fails there, and the join `X_∂ ⋈ X_∂` over `F_2` is not `D`-quantum rigid for any `D`, although each
   coordinate is rigid.

## Instances of item 2 (torsion-free)

- **`F_m × F_n` on `T_(2m) × T_(2n)`.** This recovers the product scaffold of
  `free-group-boundary-shifts-are-quantum-rigid`.
- **Burger–Mozes lattices.** Burger–Mozes (*Lattices in product of trees*, Publ. Math. IHÉS 92 (2000);
  recalled, not re-read) give torsion-free, finitely presented, **simple** cocompact lattices in
  `Aut(T_1) × Aut(T_2)`.
  - So (★′) holds over an infinite finitely presented simple group.
  - It is the first recorded instance of (★′) over a simple group, and over a non-residually-finite
    CAT(0) group.
- **Wise's lattices.** Wise's non-residually-finite complete square complexes (recalled) are another such
  family.
- **Arithmetic lattices.** Torsion-free irreducible arithmetic lattices in `PGL_2(Q_p) × PGL_2(Q_q)` are
  residually finite calibration cases.

All of these are CAT(0), so Farrell–Jones holds for them (Bartels–Lück and Wegner, recalled), and the
K-gate (K′) of the ring route is met. Boone–Higman for their subgroups was already known or is immediate:
a Burger–Mozes group is itself finitely presented and simple.

## Proof

**Item 1.**
- **Marginals.** Let `E_c(g)` be a `D`-quantum family for `X`. For each `i`, the marginal
  `E^i_a(g) = Σ_(c : c_i = a) E_c(g)` is a `D`-quantum family for `X_i`.
  - (Q1) and (Q2) are clear.
  - For (Q3): if a pattern `α_i` on `pB_D` does not occur in `X_i`, then every completion to `X` is
    forbidden. All idempotents on `pB_D` commute, so the product of marginals expands into the sum over
    completions, and every term vanishes.
- **Within one tree.** §§2–4 of `locally-finite-tree-end-shift-rigidity-proof` descend `E^i` to vertex
  idempotents `O^i_u(ε)`, one for each vertex `u` of `T_i` and each edge `ε` at `u`, and show that these
  commute among themselves. Here `O^i_u(ε)` equals the marginal at *every* site `g` with `g v = u`.
- **Across trees.** Fix `i ≠ j`, base vertices `v` of `T_i` and `w` of `T_j`, and representatives
  `c_1, …, c_s` of the `Stab(v)`-orbits on `Λ w`. Put `R = max |c_r|`.
  - Given `u = g v` and `u' ∈ Λ w`, write `g^(-1) u' = h c_r w` with `h ∈ Stab(v)`.
  - Then `u = (gh) v` and `u' = (g h c_r) w`, at sites at distance `|c_r| ≤ R ≤ 2D`.
  - So by (Q2), `O^i_u(ε)` and `O^j_(u')(δ)` commute.
- **Conclusion.** `E_c(g) = ∏_i E^i_(c_i)(g)`, by orthogonality at one site. Every factor commutes with
  every factor at every other site, so all the `E_c(g)` commute. ∎

**Item 2, factor hypotheses and coupling.**
- `Γ` has finitely many orbits of vertices and edges on each `T_i`, because it does on the product.
- **Stabilizers.** `Stab_Γ(v)` for `v ∈ T_1` acts on `T_2 × … × T_k` with finite stabilizers (`Γ` is
  discrete) and finitely many orbits. Those orbits correspond to the `Γ`-orbits of vertex tuples with
  first coordinate in `Γ v`, which are finitely many.
  - For `k = 2` it is therefore a uniform tree lattice, hence virtually free and finitely generated.
  - For `k ≥ 3` it is a cocompact lattice in a product of trees, hence finitely presented.
- **(C)** is the same finiteness of orbits.
- `Γ` is finitely presented, since it acts properly and cocompactly on a CAT(0) cube complex.

**Item 2, minimality (by induction on `k`).**
- *Case `k = 1`.* `Γ` is a uniform lattice on a leafless tree with more than two ends. So it is virtually
  free and non-elementary, `T_1` is minimal, and `∂T_1` is minimal (as in §5 of the route).
- *Step.* Let `k ≥ 2`. Take a point `(ξ_1, …, ξ_k)` and a basic open set `U_1 × … × U_k`, where `U_1` is the
  shadow of a half-tree `H`.
  - Pick an edge `e = (u_0 → u)` inside `H`, and let `S_u ⊆ U_1` be the ends through the branches at `u`
    other than the one containing `u_0`.
  - The stabilizer in `Γ` of a vertex of `T_2 × … × T_k` acts on `T_1` properly and with finitely many
    orbits, i.e. as a uniform lattice. So `Γ` is minimal on `∂T_1`. Choose `γ ∈ Γ` with `γ ξ_1 ∈ S_u`.
  - `Stab_Γ(e)` has finite index in `Stab_Γ(u)`, so it acts properly and cocompactly on `T_2 × … × T_k`.
    By induction it is minimal on `∂T_2 × … × ∂T_k`. Choose `δ ∈ Stab_Γ(e)` moving `(γ ξ_2, …, γ ξ_k)`
    into `U_2 × … × U_k`.
  - `δ` fixes `u` and `u_0`, so `δ S_u = S_u`. Hence `δγ` maps the point into the box.

**Item 2, torsion-free case.**
- **Topological freeness.** Suppose `γ ≠ 1` fixes pointwise an open box `∂H_1 × … × ∂H_k`.
  - By §5 of the route, the projection of `γ` to `Aut(T_i)` fixes a vertex `u_i ∈ H_i`.
  - So `γ` fixes the vertex `(u_1, …, u_k)`, and its stabilizer is finite, hence trivial.
- **Isotropy.** Torsion-free isotropy is automatic when `Γ` is torsion-free. ∎

**Item 3 (the wall certificate).**
- **Why (C) fails.** `Stab_(F_2)(v) = 1` has infinitely many orbits on vertices.
- **The four points.** Fix `D`. Choose ends `ξ_1 ≠ ξ_2` and `η_1 ≠ η_2` whose geodesic lines `L = (ξ_1 ξ_2)`
  and `M = (η_1 η_2)` are more than `2D` apart. `x_(ξ_1)` and `x_(ξ_2)` differ exactly at the vertices of
  `L`, and `x_(η_1)` and `x_(η_2)` differ exactly at those of `M`. The four points `(x_(ξ_a), x_(η_b))` lie
  in the join.
- **The family.** On `W = k^2`, let `Π_1, Π_2` be the coordinate projections, and `Π'_1, Π'_2` the
  projections for the basis `(e_1 + e_2, e_2)`.
  - At `g ∈ L`, put `E_c(g) = Σ_a [x_(ξ_a)(g) = c_1][x_η(g) = c_2] Π_a`. Here `x_η(g)` does not depend
    on `b`, since `g ∉ M`.
  - At `g ∈ M`, define `E_c(g)` symmetrically with the `Π'_b`.
  - Elsewhere `E_c(g)` is the scalar `[c = (x_ξ(g), x_η(g))]`.
- **Checking (Q1)–(Q3).** (Q1) is clear.
  - (Q2): sites of `L` and of `M` are more than `2D` apart, and within `L` (or within `M`) all the
    idempotents are diagonal in one basis.
  - (Q3): a ball `pB_D` meets at most one of `L` and `M`, so the product over it equals
    `Σ_a [pattern = (x_(ξ_a), x_η)] Π_a`, or the analogous sum. That vanishes on patterns not in the join.
- **Noncommutation.** The idempotents at a site of `L` and at a site of `M` do not commute. This is the
  wall certificate of `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid`. ∎

## Lesson for general BH

**Compression directions are rigid together exactly when the group couples them.**
- Cocompactness on the product of trees means that the stabilizer of a vertex of one tree acts
  cocompactly on the others. That puts any two vertex idempotents, one from each tree, at bounded
  distance in the group.
- Without that coupling, independent compression layers fail rigidity by the wall certificate.
- So (★′) is available over every torsion-free cocompact lattice on a product of trees, including
  finitely presented simple and non-residually-finite ones.
- The wall of `locally-finite-tree-end-shifts-are-quantum-rigid-sfts` persists: stabilizers are virtually
  free in each tree, and (FA) subgroups are finite. Hard (Kazhdan) inputs therefore stay out of reach of
  every locally finite tree geometry, product or not.
- A design rule follows for Track A: an input-carrying layer must be **coupled** to its compression
  scaffold through the group, never merely joined.
