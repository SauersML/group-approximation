---
rg: 2
id: seeds-record-every-bass-serre-pointer
kind: claim
title: For any splitting of a group, the pattern of a seed's translates on each thickened edge coset determines the side of the seed; if this pointer is readable in a bounded window on every edge orbit, the seed boundary maps onto the Bass–Serre boundary, so a scattered seed over a non-elementary splitting must hide some edge pointer at edge-group infinity
requires:
  - seed-compactifications-dominate-the-end-compactification
  - tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts
  - relative-seeds-glue-graphs-of-groups-into-class-c
distinct_from:
  seed-compactifications-dominate-the-end-compactification: that is the case of finite cuts (splittings over finite groups, i.e. ends); this treats arbitrary splittings, where the cut is an infinite edge coset and readability becomes a hypothesis instead of automatic.
  relative-seeds-glue-graphs-of-groups-into-class-c: that builds seeds over graphs of groups by gluing, which reads every edge pointer locally; this shows any seed must carry those pointers, and that local reading forces an uncountable boundary.
  quantum-rigidity-is-decided-on-the-derived-subshift: that puts rigidity on the perfect kernel for locally forced seeds; this shows the perfect kernel is nonempty for every seed that reads a non-elementary splitting locally.
---

**ESTABLISHED** (lane bh-star-a, 2026-09-18; elementary lane proof below; not reviewed; no priority
claimed). Notation for seeds and the gluing across cuts is as in
`seed-compactifications-dominate-the-end-compactification`: an SFT `Y` with windows `B_r`, a seed `π` on
`B_(R_0)` with (S1) and (S2), and `∂Y = Ȳ ∖ Γy_*`.

## Setting

`Γ = A ∗_H B` (generators `S_A ∪ S_B`) or `Γ = A∗_H` (generators `S_A ∪ {t}`), with Bass–Serre tree `T`.
- Let `Θ(γ) = γA`, a vertex of `T`.
- For an edge `ε` with endpoints `u` (on the `A`-side) and `w`, let `P_u(ε)` and `P_w(ε)` be the elements
  whose `Θ`-vertex lies in the component of `T ∖ ε` containing `u`, respectively `w`.
- The **cut** of `ε = gH` is `K(ε) = gH` for an amalgam, and `gH ∪ gHt` for an HNN extension.

**Cut fact.** Every edge of `Cay(Γ)` from `P_u(ε)` to `P_w(ε)` starts in `K(ε)`.
- *Amalgam.* A step `γ → γs` with `s ∈ S_B` moves `Θ` along `γA – γB – γsA`. It crosses `ε = {gA, gB}` only
  if `γA = gA` and `γB = gB`, i.e. `γ ∈ gA ∩ gB = gH`. Steps in `S_A` fix `Θ`.
- *HNN.* The step `γ → γt^(±1)` runs along the edge `γH`, respectively `γt^(-1)H`.

## Theorem

1. **Pointer lemma.** Let `x_1 = g_1.y_*` and `x_2 = g_2.y_*` have seeds deep on opposite sides of an edge
   `ε`: `g_1 ∈ P_u(ε)` and `g_2 ∈ P_w(ε)`, with `g_i B_(R_0)` at distance more than `2r` from `K(ε)`.
   Then `x_1 ≠ x_2` on `N_(2r)(K(ε))`.
2. **Readability.** Say the pointer is *readable* on the orbit of an edge `ε_0` if there are:
   - a radius `R`;
   - an anchor `p_0 ∈ K(ε_0)`;
   - a map `Ψ : A^(B_R) → {u, w}`;

   such that for every `h ∈ Γ` and every translate `x = g.y_*` whose seed is at distance more than `R` from
   `K(hε_0)`, `Ψ((h^(-1).x)|_(p_0 B_R))` is the side of `g` relative to `hε_0`.
   - If the pointer is readable on every edge orbit and the splitting is non-elementary, then every end `ζ`
     of `T` has a point `z_ζ ∈ ∂Y` that determines `ζ`. So `∂Y` has cardinality at least that of `∂T`,
     and it is uncountable.
3. **Finite edge groups.** If `H` is finite, readability is automatic (take `R` to cover the finite set
   `N_(2r)(K(ε_0))`). This recovers the end domination of the parent node for one-edge splittings.
4. **Scattered seeds.** A countable seed compactification of a non-elementarily split group has an edge
   orbit on which the pointer is **hidden**. For every `R` and anchor `p_0`, there are translates `x_1, x_2`
   and orbit edges `h_1ε_0, h_2ε_0`, with seeds deeper than `R`, such that
   `(h_1^(-1).x_1)|_(p_0 B_R) = (h_2^(-1).x_2)|_(p_0 B_R)` but the framed sides are opposite.

## Proof

**1.**
- `Γ ∖ K(ε)` has no component meeting both `P_u` and `P_w`, by the cut fact.
- Put `N = N_(2r)(K(ε))`, and suppose `x_1 = x_2` on `N`. Define `x = x_1` on `(P_u ∖ K(ε)) ∪ N` and
  `x = x_2` elsewhere.
- A window `pB_r` meeting both `P_u ∖ N` and `P_w ∖ N` would contain a path of length `≤ 2r` crossing
  `K(ε)`, which is impossible. So every window of `x` is a window of `x_1` or of `x_2`, and `x ∈ Y`.
- `x` carries the seed at `g_1` and at `g_2`. By (S1) and (S2), `g_1 = g_2`, which contradicts
  `P_u ∩ P_w = ∅`. ∎

**2.** Let `ζ ∈ ∂T`, and choose `g_n` with `Θ(g_n) → ζ`. Pass to a subsequence with `g_n.y_* → z_ζ`.
- `Θ` is Lipschitz, so `g_n → ∞`, and `z_ζ ∈ ∂Y`.
- Fix an orbit edge `ε = hε_0`. For large `n` the seed `g_n` is deep on the `ζ`-side of `ε`. So
  `Ψ((h^(-1) g_n.y_*)|_(p_0 B_R))` is the `ζ`-side.
- The restriction `(g_n.y_*)|_(hp_0 B_R)` is eventually equal to `z_ζ|_(hp_0 B_R)`. So
  `Ψ((h^(-1).z_ζ)|_(p_0 B_R))` is the side of `ζ` relative to every edge of every orbit.
- Distinct ends are separated by some edge, so `ζ ↦ z_ζ` is injective.
- `∂T` contains a Cantor set when the action is non-elementary (ping-pong). ∎

**3–4.** Part 3 is immediate from part 1: `N_(2r)(K(ε_0))` is finite. Part 4 is the contrapositive of
part 2, applied to the edge orbits of any non-elementary splitting. ∎

## Instances and consequences

- **All glued seeds read their pointers.** In tree gluing (bf61de7d0), relative gluing (5deee0184), and
  the BS(1,2) seed (f6aedfd93), each element carries its orientation letter. So the pointer is readable
  with `R = 1`, and `∂Y ↠ ∂T` (in the sense of part 2).
  - For non-elementary trees, every glued seed of the SEED TOWER programme therefore has an uncountable
    boundary.
  - With `quantum-rigidity-is-decided-on-the-derived-subshift`, its rigidity must be paid on a perfect
    kernel carrying `∂T`. For towers, the quantum side of CAP is live, not free.
- **Products `Λ × H`.** A splitting of `Λ` over a finite `F` induces `Λ × H = (A × H) ∗_(F × H) (B × H)`,
  with cut columns `g(F × H)`.
  - So a seed over `Λ × H` records the `Λ`-pointer on every column, and a product seed `Y_0 ⊠ C` reads it
    locally.
  - **Answer to the coordinator's question (partial).** An infinitely ended `Λ_0` admits a scattered seed
    over `Λ_0 × Z` only if that seed hides the pointer on some column orbit (part 4). No product or glued
    construction does, so none of those is scattered. Radial (light-cone) attempts fail heuristically (next
    bullet). The existence of pointer-hiding seeds is **open**.
- **Why hiding looks hard (heuristic, not claimed).** Pushing the pointer to large heights, e.g. a
  light-cone of arrival times from the origin, creates *fronts*. Near a front, the pointers of a whole
  tree-ball are visible at once, and limits along fronts are horofunction configurations, one per end, so
  the boundary is again uncountable.

## Conjecture and CAP

**Conjecture (HP).** Seeds cannot hide pointers: every seed over a non-elementarily split group has an
uncountable boundary.

Under (HP):
- scattered seeds exist only over groups all of whose splittings are elementary, such as polycyclic
  groups, groups with (FA), and one-ended groups without such splittings;
- CAP_sc of `seed-compactifications-dominate-the-end-compactification` is then a question about those groups
  alone;
- machine towers built by non-elementary splittings can never be scattered, so they must beat CAP on a
  perfect kernel, where rigidity costs something.

## Lesson for general BH

**Every splitting leaves a pointer in the seed.** Gluing a seed with a translate across an edge coset
would create a second origin, so the pattern on each edge coset records which side the origin is on.
- If a bounded window reads that pointer, as in every glued or product construction, the seed boundary
  carries the whole Bass–Serre boundary.
- So the seed programme's towers are never scattered, and their rigidity must be earned on a perfect
  kernel.
- The rigidity-free CAP_sc route survives only for groups without non-elementary splittings, or for seeds
  that hide pointers at edge-group infinity. None of the latter is known.
