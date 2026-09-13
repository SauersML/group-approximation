---
rg: 2
id: product-of-trees-faithful-factor-pbh-via-bass-serre-induction
kind: route
title: Induct on the number of factors for finite presentation, then feed separating factor images to the rigid permutation group theorem
target: product-of-trees-lattices-with-faithful-factor-satisfy-pbh
requires: [faithful-finite-index-graphs-of-groups-have-type-a-overgroups, boone-higman-type-a-class-closed-under-finite-extensions]
---

Notation is as in the target. An action on a product is **factorwise** when
`σ` is trivial for every element. For an edge `e` of a tree, `Delta_e` fixes
both endpoints and `Delta_{e}` is the setwise stabilizer.

## Lemma P

Let `Delta` act factorwise on `Y = S_1 x ... x S_m` (`m >= 0`, locally finite
trees) with finite vertex stabilizers and finitely many vertex orbits. Then:
- **(P1)** for a vertex `v` and an edge `e` of `S_1`, the groups `Delta_v`,
  `Delta_e` and `Delta_{e}` act factorwise on `Y' = S_2 x ... x S_m` with finite
  vertex stabilizers and finitely many vertex orbits;
- **(P2)** `Delta` is finitely presented.

*Proof of (P1).*
- **Stabilizers.** `Stab_(Delta_v)(w) = Stab_Delta((v,w))` is finite. For an
  endpoint `v` of `e`, `Stab_(Delta_e)(w) <= Stab_Delta((v,w))`, and it has index
  at most 2 in `Stab_(Delta_{e})(w)`.
- **Orbits.** If `delta (v,w) = (v,w')` then `delta ∈ Delta_v`. So
  `[w] ↦ [(v,w)]` injects `Delta_v \ V(Y')` into the finite set
  `Delta \ V(Y)`. Next, `[Delta_v : Delta_e] <= deg(v)`, so each `Delta_v`-orbit
  splits into finitely many `Delta_e`-orbits. The overgroup `Delta_{e}` has no
  more orbits than `Delta_e`.

*Proof of (P2), by induction on `m`.*
- **`m = 0`.** `Y` is a point, so `Delta` is finite and finitely presented.
- **Finite quotient.** For `m >= 1`, let `S_1'` be the barycentric subdivision.
  `Delta` acts on it without inversions. The vertex orbits on `S_1` are
  projections of vertex orbits of `Y`, so there are finitely many. Every edge
  meets a representative vertex of finite degree, so `Delta \ S_1'` is finite.
- **Graph of groups.** By the structure theorem (Serre, *Trees*, §I.5.4; not
  re-read), `Delta` is the fundamental group of a finite graph of groups. Its
  vertex groups are conjugates of `Delta_v` and `Delta_{e}`, and its edge groups
  are conjugates of `Delta_e`.
- **Vertex and edge groups.** By (P1) and the induction hypothesis for `m - 1`
  factors, the vertex groups are finitely presented. The edge groups have finite
  index in them, so they are finitely generated (Schreier).
- **Presentation.** The standard presentation (Serre §I.5.1, quoted in BLIW
  arXiv:2408.05673v2 §10) takes:
  - as generators, the vertex generators and one letter `t_e` per edge off a
    maximal tree;
  - as relators, the vertex relators and `t_e φ_ι(g) t_e^(-1) = φ_τ(g)` for
    `g ∈ G_e`, with `t_e = 1` on tree edges.

  For fixed `e`, the `g` satisfying this relation form a subgroup. So it suffices
  to impose it for a finite generating set of `G_e`, and `Delta` is finitely
  presented. `∎`

## Items 1–3

- **Item 1.** `Gamma_0` has finite index, so it acts factorwise with finite
  vertex stabilizers and finitely many orbits. By (P2) it is finitely presented.
  `Gamma` is a finite-index overgroup of `Gamma_0`, so it is finitely presented
  too (standard, not re-read).
- **Item 2.** For `i ∈ I` put `P_i = pr_i(Gamma_0) <= Aut(T_i)`.
  - **Hypotheses of item 2 of the rigid-permutation claim.** `P_i` acts
    faithfully on `T_i`. Every vertex of `T_i` is a coordinate of a vertex of
    `X`, so `P_i` has finitely many vertex orbits. `T_i` is locally finite, and
    the edge stabilizers are finitely presented by hypothesis. So
    `faithful-finite-index-graphs-of-groups-have-type-a-overgroups` (item 2)
    gives `P_i ∈ B_A`.
  - **Edge stabilizers.** `pr_i(gamma)` fixes `e` exactly when
    `gamma ∈ Gamma_(0,e)`, and `K_i <= Gamma_(0,e)`. So
    `Stab_(P_i)(e) ≅ Gamma_(0,e) / K_i`.
    - `Gamma_(0,e)` is finitely presented by (P1) and (P2), after reordering
      factors so that `T_i` comes first.
    - A quotient of a finitely presented group is finitely presented iff its
      kernel is the normal closure of finitely many elements (standard).
  - **Conclusion.** `∩_(i ∈ I) K_i = 1`, so `gamma ↦ (pr_i(gamma))_(i ∈ I)`
    embeds `Gamma_0` in `∏_(i ∈ I) P_i`. Item 1 of
    `boone-higman-type-a-class-closed-under-finite-extensions` (subgroups and
    finite products) gives `Gamma_0 ∈ B_A`. Its item 2 gives `Gamma ∈ B_A`, and
    its item 3 gives the envelopes and solvable word problem.
- **Item 3.** Take `I = {i}`. Then `K_i = 1`, and
  `Stab_(P_i)(e) ≅ Gamma_(0,e)` is finitely presented by (P1) and (P2). Apply
  item 2.

## Item 4

Let `rho : Gamma_0 -> H_i` be the coordinate map and `D = rho(K_i)`.
- **Injective.** If `gamma ∈ K_i` and `rho(gamma) = 1`, then `gamma` fixes every
  vertex of `X`. So `gamma = 1` by faithfulness on `X`.
- **Discrete.** Fix a vertex `v` of `T_i` and a vertex `w` of
  `∏_(j ≠ i) T_j`. `U = Stab_(H_i)(w)` is open. Elements of `K_i` fix `v`, so
  `D ∩ U = rho(Stab_(K_i)((v,w)))` is finite. `H_i` is Hausdorff, so removing
  the finitely many non-identity points of `D ∩ U` leaves an open neighbourhood
  of `1` meeting `D` only in `1`.
- **Normalized by `L_i`.** `D` is discrete, hence closed. `N_(H_i)(D)` is
  therefore closed, and it contains `rho(Gamma_0)` because `K_i` is normal. So it
  contains `L_i`, and `D <= rho(Gamma_0) <= L_i`.
- **In the quasi-centre.** For `d ∈ D`, the map `L_i -> D`, `l ↦ l d l^(-1)` is
  continuous into a discrete space. So `C_(L_i)(d)`, the preimage of `d`, is
  open, and `d ∈ QZ(L_i)`.

Hence `QZ(L_i) = 1` forces `K_i = 1`. `∎`
