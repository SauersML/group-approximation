---
rg: 2
id: core-marked-gluing-of-relative-seeds
kind: claim
title: A subgroup acting on a Bass–Serre tree with finite core and full stabilizers on core edges has a rigid relative seed as soon as its vertex pieces and all edge groups do; the core replaces the sink
distinct_from:
  relative-seeds-glue-graphs-of-groups-into-class-c: that marks one vertex coset as the sink, so the stabilizer lies in a vertex group; this marks a whole finite-quotient core subtree, so the stabilizer may span several vertex groups and stable letters.
  kurosh-relative-seeds-and-the-b1-digit-splitting: that (Theorem K) is the free-product star case, obtained by re-splitting and the vertex-marked theorem; this is the general core-marked form, with arbitrary vertex groups and HNN or amalgam edges, under full core-edge stabilizers.
---

**ESTABLISHED** by the proof below (lane bh-invent-03, 2026-09-18; elementary lane proof, not reviewed; no priority
claimed). Notation and lemmas (L0), (L1), atoms and the F-trick are as in `relative-seeds-glue-graphs-of-groups-proof`.
Answers bh-invent-14's request on `board/seed-tower.md`.

## Statement

**Data.** `𝔾` is a finite graph of finitely generated groups, `Λ = π_1(𝔾)`, and `T` its Bass–Serre tree. Let
`S ≤ Λ` and let `K ⊆ T` be an `S`-invariant subtree (the **core**) with:
- (K0) `S\K` finite;
- (FE) **full core edges**: every edge `e` of `K` has `S_e = Λ_e`;
- (KV) for every vertex `v = hV_u` of `K`, the **piece** `S'_v = h^(-1) S_v h ≤ V_u` has `(V_u, S'_v) ∈ 𝓡`;
- (E) for every oriented edge `ε` of `𝔾`, `(V_(o(ε)), C_ε) ∈ 𝓡`. This is used for pointers toward `K`.

**Conclusion.** Then `(Λ, S) ∈ 𝓡`. No vertex group needs to lie in `𝒞`.

**Special cases.**
- `K` a single vertex is the vertex-marked item 1 of `relative-seeds-glue-graphs-of-groups-into-class-c`.
- Trivial edge groups give Kurosh subgroups of free products with finite core, of which Theorem K of d13f60e6f is
  the star case. (FE) is automatic there.
- Finite-index core pieces give Hall-type completions.

## Proof

**Core edges are read locally.** At a core vertex of class `p` (its `S`-orbit), the core edges of type `ε` form
finitely many `S'_p`-orbits. By (FE), each orbit is a single right coset `S'_p a_(p,ε,k)`, since
`a C_ε a^(-1) ⊆ S'_p` gives `S'_p a C_ε = S'_p a`. So the edge `(ε, xC_ε)` is a core edge of data `k` iff `y_*^p` has
a seed at `x a_(p,ε,k)^(-1)`. That is a local pattern, and it does not depend on the representative `x`.

**Coordinates.** Each vertex type `u` has one coordinate. It records either:
- *core of class `p`* (a class of type `u`), with a letter of `Y_p`, the rigid relative seed for `(V_u, S'_p)`; or
- *out of type `ε`*, with a letter of `Y_ε`, the rigid relative seed for `(V_u, C_ε)`.

**Rules.**
- (T) The class or type is constant along `V_u`. (Y) Configurations obey their SFTs.
- (K1) **Core edges, both directions.** For each core edge datum `(p, ε, k)` with reverse datum `(q, ε̄, k')`:
  - "`v` core of class `p` with a seed at `x a_k^(-1)`" holds
  - iff "the vertex across the edge at `x` is core of class `q` with a seed at `x t_ε a_(k')^(-1)`".
- (K2) **Exclusivity.** On every edge exactly one of three things holds: it is a core edge, the first endpoint is
  out and points along it, or the second endpoint is out and points along it. "Points along" means type `ε` with
  a `Y_ε`-seed at the edge element, as in 5deee0184.

**(RS1).**
- **The seed.** Take the pattern "class `p_0` with `π_(p_0)` at `1`". It fixes the base core configuration.
- **The core is pinned.** By (K1), each core neighbour has a seed at a prescribed element, hence a unique
  configuration. The core is connected, so all of `K` is pinned.
- **Consistency.** The pinned configurations are consistent because the `S`-equivariant configuration exists.
  (FE) on the far side makes the prescribed seeds independent of the representative of the edge coset.
- **Out vertices.** They point to their nearest-point projection on `K`, forced as in 5deee0184.
- **Stabilizer contains `S`.** The configuration is `S`-invariant by construction.
- **Stabilizer is at most `S`.** If `g` fixes `y_*`, then `g v_0` is core of class `p_0`, so `g v_0 = s v_0` with
  `s ∈ S`. Then `s^(-1) g` fixes `v_0` and its configuration, so it lies in `S_(v_0)`. Hence
  `Stab(y_*) = S`.

**(RS2).** Four kinds of point, each a limit of translates of `y_*`:
- **A seedless core vertex.** `z = lim a_n.y_*^p` with `a_n S'_p -> ∞`. Its core edges `a_n S'_p a_k` also escape.
  So the limit is a sink core vertex with all neighbours pointing in, as for 5deee0184's seedless sinks.
- **Pointers converging to an end.** Move `K` away along that end.
- **Out sinks.** As in 5deee0184.
- **Translates of `y_*`.**

**Rigidity.**
- **Each coset algebra.** For each vertex `v`, let `𝒜_v` be the commutative algebra of letters at `v`. It is
  commutative by rigidity of `Y_p` or `Y_ε` and the F-trick, with class and type indicators constant along the
  coset.
- **Its atoms.**
  - Pointer events `Π_v(f)`.
  - Core-edge events `κ_v(p)[seed_p at x a_k^(-1)]`. Each seed cylinder is one point, so these are atoms.
- **The three edge events.** On an edge `f_i = v_(i−1)v_i` write:
  - `B_i`: `v_(i−1)` points forward;
  - `C_i`: `v_i` points back;
  - `Γ_i`: `f_i` is a core edge, a finite sum of orthogonal atoms.
  By (K1), (L1) and (L0), each atom of `Γ_i` is **the same operator** in `𝒜_(v_(i−1))` and in `𝒜_(v_i)`. By (K2),
  `B_i + C_i + Γ_i = 1`, and all three lie in `𝒜_(v_(i−1))` and in `𝒜_(v_i)`.
- **Monotonicity.** `C_i ≤ C_(i+1)`. Indeed, if `v_i` is out and points back, it does not point along `f_(i+1)`
  (orthogonal pointer atoms), and `f_(i+1)` is not a core edge (out and core are orthogonal types). This is a
  directed implication, as `fate-couplings-are-rigid-only-along-directed-implication-chains` (2e723c93e) requires.
- **Core atoms follow the path.** Let `γ` be an atom of `Γ_1`. Then `γ` is an atom of `𝒜_(v_1)`, so exactly one of
  `γ ≤ C_2` or `γ = γ'` for a unique atom `γ'` of `Γ_2` holds, since `γB_2 = 0`. By induction, either `γ ≤ C_j`
  for some `j`, or `γ` is an atom of `𝒜_(v_m)`.
- **Two vertices `v = v_0` and `w = v_m`.** Let `X ∈ 𝒜_v`. Then `X = XB_1 + XΓ_1 + XC_1`.
  - `XC_1 ≤ C_1 ≤ C_m`, an atom of `𝒜_w`, so it commutes with `𝒜_w` by domination.
  - `XΓ_1` is a sum of atoms of `Γ_1`. Each is `≤ C_m` or an atom of `𝒜_w`, so it commutes with `𝒜_w`.
  - `XB_1 ∈ {0, B_1}`, and `B_1 = 1 − Γ_1 − C_1` commutes with `𝒜_w` by the two previous cases.
- **Conclusion.** Letters at different vertices commute, letters at one vertex commute, and coordinates at one
  site commute by Q1. So the SFT is `D`-quantum rigid for large `D`. ∎

## Without (FE)

When `S_e ⊊ Λ_e` on a core edge, two things fail.
- **Neighbour pinning.** Local rules then determine the neighbour's configuration only up to a twist by
  `Λ_e / S_e`.
- **Local reading of core edges.** The double cosets `S'_p a C_ε` need not be locally readable.
- **The repair needed.** An **edge-pinned** relative seed: one whose restriction to the edge cosets pins the
  `C_ε`-position across `φ_ε`. It is not supplied here.

**For the tower.** Check (FE) first on each pair that bh-invent-14's B_1 re-split produces:
`(Z_J, F(a))`, `(J, Q)` with `Q = F(a) * ⟨t⟩`, and `(J_Q, F(a))`.

## Lesson for general BH

**The sink generalizes to a core.** Any subgroup that is a sub-graph-of-groups with full edge stabilizers inherits
a rigid relative seed from its vertex pieces.
- **Rigidity along the tree.** It still comes only from directed implications: pointers monotone toward the core,
  and core atoms shared across edges.
- **The only obstruction.** The seed tower's Kurosh and HNN steps are now reduced to the edge-twist condition
  (FE), i.e. whether the subgroup contains the whole edge group on each of its core edges.

## Referee (bh-ref-kourovka-a, 2026-09-19): PASS

I checked the proof line by line against `relative-seeds-glue-graphs-of-groups-proof` (refereed PASS):
its atoms (A), exclusivity (B), chains (C), domination (D) and the F-trick.

- **Core edges are read locally.**
  - Oriented core edges at `v` of type `ε` lie in finitely many `S_v`-orbits: an `s ∈ S` matching two
    of them fixes their common origin, and `S\K` is finite.
  - (FE) gives `aC_εa^(-1) ⊆ S'_v`, so each orbit is the right coset `S'_p a_k`.
  - Seeds of `y_*^p` lie exactly on `S'_p`, so "core of datum `k` at `x`" iff there is a seed at
    `x a_k^(-1)`. By (FE) this is independent of the representative `x ∈ xC_ε`.
- **(RS1).** From the base seed, (K1) pins each core neighbour. Its class and a seed at a
  prescribed element give a unique `Y_q`-configuration. Non-core edges at core vertices force out
  neighbours pointing in, by (K2), and each out vertex points along exactly one edge. So the
  cylinder is `{y_*}`.
  - A class-`p` seed at `e` forces the translate `(e h_p^(-1)).y_*`, by uniqueness.
  - `Stab = S`: `g v_0 = s v_0`, and then `s^(-1)g ∈ S_(v_0)`.
- **(RS2).** The four kinds are exhaustive.
  - A seeded core vertex pins a translate of the whole point.
  - A seedless core vertex has no core edges, so it is a sink with everything pointing in.
  - With no core vertex, this is the base orientation argument.
  - Each kind is a limit of translates. For the seedless core sink, the core edges `a_nS'_pa_k` leave
    every finite window, so the window sees only the sink and pointers toward it.
- **Rigidity.**
  - (K1) is an equivalence of two local events, so (L0) and (Q2) make the core atoms the **same
    operator** at both endpoints.
  - `B_i + C_i + Γ_i = 1`, with all three in both endpoint algebras.
  - `C_i ⊥ B_(i+1)` (distinct pointer atoms) and `C_i ⊥ Γ_(i+1)` (out versus core), which gives
    `C_i ≤ C_(i+1)`.
  - A core atom `γ` has `γB_2 = 0`, so either `γ ≤ C_2` or `γ` equals the unique atom of `Γ_2` below
    it. Two atoms with `γ ≤ γ''` are equal.
  - Every piece of `X = XB_1 + XΓ_1 + XC_1` is dominated by an atom of `𝒜_w` or equals one.

  Correct.
- **Special cases.** A single-vertex `K` gives the vertex-marked item 1, and trivial edge groups make
  (FE) automatic. Both are correct.

**Minor.**
- State the convention that each class `p` has a base vertex `h_pV_u`, with `S'_p = h_p^(-1)S_(v_p)h_p`,
  and that other vertices of the class use representatives `s h_p`. This is what makes "a seed at
  `x a_k^(-1)`" canonical.
- The "Without (FE)" section is a correct diagnosis, not a theorem.
