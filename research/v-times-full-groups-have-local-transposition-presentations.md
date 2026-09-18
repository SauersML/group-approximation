---
rg: 2
id: v-times-full-groups-have-local-transposition-presentations
kind: claim
title: The full group of V times a free Lambda-subshift is presented by transpositions of product pieces subject to order, conjugacy and two-directional split relations; with lifts in the gluing group this would make the gluing presentation exact (K = 1)
distinct_from:
  v-times-sft-gluing-kernel-is-relatively-perfect: that shows the gluing kernel is relatively perfect, so centrality is equivalent to exactness; this states a local (Quick-type) presentation of the full group from which exactness would follow.
  v-times-sft-full-groups-glue-from-two-wreath-pieces: that is P2'b, finite normal generation of the gluing kernel; this is a stronger, dynamics-free statement about the full group itself, together with a route to K = 1.
  v-times-minimal-free-sft-alternating-full-groups-are-fp: that is P2 (finite presentation, refuted in general); an infinite local presentation says nothing about finiteness, which needs finitely many orbits of relation configurations and fails without rigidity.
---

**OPEN.**

## Statement

Notation as in `v-times-sft-full-groups-split-into-two-wreath-pieces`: `T = G_V × (Λ ⋉ X)` on
`Ω = C × X`, with `X` a free subshift. A *piece* is `[u] × P`, with `u` a finite word and `P ⊆ X`
a cylinder. A *basic transposition* `[α | β]_λ` exchanges disjoint pieces `α = [u] × P` and
`β = [u'] × λP` by `(u w, x) ↔ (u' w, λ x)`.

Claim: `F(T)` is presented by the basic transpositions, subject to:
- (O) `[α | β]_λ^2 = 1`;
- (C) conjugacy: `[α | β]_λ^([γ | δ]_μ) = [α•, β•]`, whenever the images of `α, β` under `[γ | δ]_μ`
  are pieces (Quick's partial action, with labels);
- (S_C) split in the Cantor direction: `[α | β]_λ = [α0 | β0]_λ [α1 | β1]_λ`;
- (S_X) split in the subshift direction: `[α | β]_λ = [α_(P_1) | β_(λP_1)]_λ [α_(P_2) | β_(λP_2)]_λ`
  for a cylinder partition `P = P_1 ⊔ P_2`.

## Evidence

- **`X` a single `Λ`-orbit with `Λ = Z/n`.** Then `F(T) = V_(2,n) ≅ V`, and the claim is the
  Bleak--Quick transposition presentation of `V` (Quick, arXiv:1901.04409v2, §1, crediting Bleak--Quick).
  It is read at source only through Quick's summary.
- **Brin--Thompson groups.** With `Λ ⋉ X` replaced by `G_V^(n−1)`, the analogue is Quick's
  Theorem `thm:infpres` for `nV`: generators the transpositions of disjoint addresses, and relations
  (O), (C) and the split relations in every coordinate. This was read from the TeX via MSI.
- **Dynamics.** No relation mentions the SFT structure. Rigidity would enter only in a
  finite-orbit reduction of (C) and (S_X), which is how Quick passes to finite presentations. Here
  that step fails without rigidity, consistent with the necessity theorem.

## Route to exactness of the gluing group

Assume the claim. Define lifts `L[α | β]_λ ∈ Γ~`:
- if `λ = 1` and `u ⊥ u'`: `(u u')^[P] ∈ N_X`;
- if `u ⊥ u'`: `L = m^-1 (u u')^[λP] m` with `m = λ|_([u]) ∈ M`;
- if `u, u'` are comparable: conjugate by `v^[λP] ∈ N_X` moving `[u']` onto a cone incomparable
  with `u`, as in §1 of `v-times-sft-full-groups-split-into-two-wreath-pieces-proof`.

The first two formulas are checked in `F(T)` by direct evaluation on points. If (O), (C), (S_C), (S_X)
hold for the lifts in `Γ~`, and every generator of `M` and `N_X` equals in `Γ~` the product of
lifts of its transposition decomposition, then `F(T) → Γ~` is a section whose image contains
`M ∪ N_X`. So `π` is an isomorphism and `K = 1`.

**Checked here** (lane argument, using (R1) and (R2) of `v-times-sft-gluing-kernel-is-relatively-perfect`):
- **(O)** for all lifts: conjugates of involutions.
- **(S_C)** for the first two lift types.
  - `λ = 1`: this is a relation of `N_X`.
  - `λ ≠ 1`: `m = λ|_([u0]) λ|_([u1])`. The factor `λ|_([u1]) ∈ M_([u1])` commutes with
    `(u0 u'0)^[λP] ∈ N_([u0] ∪ [u'0])` by (R1), since `u ⊥ u'`.
- **(S_X)** for the first two lift types. `(u u')^[λP] = (u u')^[λP_1] (u u')^[λP_2]` in `N_X`.
- **Disjoint commutation** (the case of (C) with disjoint supports), in the representative case
  of a cross lift `L = m^-1 n m` against `n_2 = (w w')^[Q]` with `[w] ∪ [w'] ⊆ [u]`. By (R2),
  `m n_2 m^-1 = λ n_2 λ^-1 = (w w')^[λQ]`, which commutes with `n = (u u')^[λP]` in `N_X` when the
  supports are disjoint.

**Not checked:**
- (C) for overlapping supports;
- independence of the comparable-case lift from its choices, which is itself an instance of (C);
- the decomposition of the generators of `M` and `N_X`.

## Lesson for general BH

Finite presentation of `V × G` full groups has two layers:
- a dynamics-free infinite local presentation, of Coxeter type, by transpositions with conjugacy
  and split relations;
- a finiteness step that folds the relation configurations into finitely many orbits.

Rigidity lives only in the second layer. The gluing gate P2′b is the first layer, so it can be
attacked like Quick's proof for `nV`, with no subshift input.
