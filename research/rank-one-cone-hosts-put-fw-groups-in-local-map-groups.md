---
rg: 2
id: rank-one-cone-hosts-put-fw-groups-in-local-map-groups
kind: claim
title: In a full group whose cones form a tree, every FW subgroup virtually embeds in a finite power of the local-map groupoid, so an infinite simple Kazhdan subgroup is already a group of local maps
distinct_from:
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: that is the case of synchronous local maps (a self-similar H <= Aut(T_d)) on the full d-ary tree; this allows any self-similar groupoid of cone-to-cone homeomorphisms on the path space of a finite graph, asynchronous ones included, and identifies the local-map groupoid as the only place an FW group can sit.
  almost-v-fw-subgroups-act-through-finitely-many-germs: that treats finitely many singular points over V, where FW groups land in germ groups; this treats cone hosts with no singular points but arbitrary local maps. Together they say that in rank one an FW input is always carried by a local group.
  finitely-coded-cantor-actions-give-type-a-hosts: that is the positive host machine for finitely coded groupoids of every rank; this is the rank-one limit of that machine, and the reason Kazhdan inputs need non-tree cone structures.
---

**ESTABLISHED** through `rank-one-cone-hosts-fw-local-map-proof`. It is a lane proof and elementary: the proof of `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf-proof` with the self-similar group replaced by a self-similar groupoid. It has not been independently reviewed, and no priority is claimed, since the commensurated-cone argument is standard.

## Setting

- **Path spaces.** `E` is a finite directed graph. For a vertex `v`, `X_v` is the space of one-sided infinite paths starting at `v`. `R` is a finite set of root vertices, and `X = ⊔_{r in R} X_r`.
- **Cones.** For a finite path `u` from a root, `β_u : X_{t(u)} -> X` is `ζ -> uζ`, and its image `uX` is the *cone* of `u`. Two cones are nested or disjoint, so the cones form a locally finite tree.
- **Local-map groupoid.** `Λ` is a groupoid of homeomorphisms `λ : X_v -> X_w` between vertex path spaces. It contains the identities and is closed under composition and inversion. It is **self-similar** (SS): for each `λ : X_v -> X_w`, all but finitely many paths `z` from `v` satisfy both
  - `λ(zX) = z'X` for some path `z'` from `w`, and
  - `λ|_z := β_{z'}^{-1} ∘ λ ∘ β_z` lies in `Λ`.
  `Λ(v)` denotes the vertex group of `Λ` at `v`.
- **Cone host.** `F(Λ)` is the group of homeomorphisms `f` of `X` for which there are a finite complete prefix code `{u_i}` of paths from roots, paths `y_i`, and elements `λ_i in Λ` with `f(u_i ζ) = y_i λ_i(ζ)`. The statement applies to every subgroup `G <= F(Λ)`.

## Statement

1. **Cone markings are commensurated.** Call an injective map `φ : X_v -> X` a *Λ-piece map* if, on some finite complete prefix code, it has the form `w_j ζ -> y_j λ_j(ζ)`. Let `S` be the set of classes `[φ] = φ∘Λ(v)`. `F(Λ)` acts on `S` by `f·[φ] = [f∘φ]`, and the set `M = {[β_u]}` of cone classes is commensurated.
2. **FW transfer.** Suppose `G <= F(Λ)` has property FW; property (T) implies FW. Then some finite-index `G_0 <= G` has an injective homomorphism `G_0 -> Λ(v_1) x ... x Λ(v_m)`.
3. **Simple inputs.** If `G` is infinite, simple and FW, for example an infinite simple Kazhdan group, then `G` embeds in a single vertex group `Λ(v)`.

## Consequences

- **Trivial local maps.** Every FW subgroup is finite when `Λ` consists of identities. That covers:
  - Thompson's `V`;
  - the Higman–Thompson groups `V_{n,r}`;
  - Matui's topological full groups of one-sided shifts of finite type, and more generally the full groups of path-space groupoids of finite graphs.
  For `V` itself this is the Kazhdan case of `thompson-v-has-haagerup-property`; here it holds for FW and for every graph.
- **Synchronous local maps.** Every FW subgroup is residually finite when `Λ` consists of tree automorphisms, with `λ(zX) = λ(z)X` for every `z`. This covers:
  - Röver–Nekrashevych groups `V_{d,r}(H)`;
  - Exel–Pardo and Katsura self-similar graph actions.
  So no infinite simple Kazhdan group embeds in any of these. For Katsura's one-vertex odometers, with `Λ(v) = Z`, every FW subgroup is finite.
- **Rank one is local.** The reduced inputs of `boone-higman-iff-simple-kazhdan-decidable-inputs` are the infinite finitely generated simple Kazhdan groups with solvable word problem.
  - Such a group lies in a rank-one cone host only if it is already a subgroup of one vertex group of that host's local-map groupoid.
  - With synchronous local maps that is impossible, by residual finiteness.
  - So a rank-one construction can only move a Kazhdan input into its local maps; it never makes room for one.
  - The only rank-one hosts left for such inputs have asynchronous local maps. These are the rational (transducer) groupoids of rational similarity groups, which apply whenever (SS) holds (checked here only in the synchronous cases).
  - Together with `almost-v-fw-subgroups-act-through-finitely-many-germs`, which covers the singular points of V-germ extensions, including shells and Houghton-like envelopes, this covers every rank-one host family on main.

## Scope

Nothing is claimed when the cones do not form a tree. That includes:
- `nV` for `n >= 2`;
- k-graph full groups with `k >= 2`;
- tree-product and Ã₂ lattice hosts;
- `𝒯_m` for `m >= 2`;
- twisted Brin–Thompson groups `SV_G`;
- the twisted integral-affine groups `W`.

Infinite Kazhdan groups do occur there: every cocompact Ã₂ lattice lies in the full group of a finite 2-graph (`a2-lattices-embed-in-fp-simple-groups`). The commensuration in item 1 fails exactly when a cone can meet two pieces of a code without lying in either, which happens for infinitely many cones once the cone poset is not a tree.

**Lesson for general BH.** FW rigidity turns every rank-one host into a statement about its local maps. So progress on the reduced (simple Kazhdan) inputs has two options:
- non-tree cone structures (rank at least 2, product or building boundaries, polyhedral dissections);
- genuinely asynchronous local-map groupoids that already contain the input.
