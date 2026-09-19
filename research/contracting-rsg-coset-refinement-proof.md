---
rg: 2
id: contracting-rsg-coset-refinement-proof
kind: route
title: Label cones by a cocycle of canonical similarities, refine the graph by right cosets, and read canonical similarities in Γ' off equal cosets; recurrent components of the refined graph are the loop-group orbits
target: contracting-rsgs-pass-to-finite-index-subgroups-via-loops
requires:
  - contracting-rsgs-closed-under-finite-index-overgroups
  - sft-irreducible-core-iff-unique-recurrent-component
---

Lane `bh-partials`, lane proof, not reviewed. Notation is that of the target.

**Step 0 (roots).**
- Write `E` as a disjoint union of proper cones `[ρ_1], …, [ρ_m]`. If `E` is a single cone, use its children.
- Choose root labels `ℓ_{ρ_i} ∈ G` restricting to the canonical similarity `[α_{t(ρ_i)}] → [ρ_i]`. These exist by the RSG
  property, and so do the `k_e`.
- For `β = ρ_iγ` put `ℓ_β = ℓ_{ρ_i}·k_{γ_1}⋯k_{γ_r}`.
- By induction `ℓ_β` restricts to the canonical similarity `[α_{t(β)}] → [β]`. The step: `k_e` maps `[α_{u'}]` onto
  `[α_u e]` canonically, and `ℓ_β` maps `[α_u e]` onto `[βe]` canonically, so `ℓ_{βe} = ℓ_βk_e` works.

**Step 1 (the refined coding).**
- `Γ̃` has vertices `(u, c)`, `c ∈ Γ'∖G` (right cosets), and edges `(u,c) → (u', ck_e)`. Add root vertices `r_i`, copies
  of `(t(ρ_i), Γ'ℓ_{ρ_i})` with no incoming edges. Keep only the vertices reachable from the `r_i`.
- **Coding space.** Put `Ẽ = ⋃ [r_i]`, and let `ψ : E → Ẽ` send `ρ_iγ` to the unique lift of `γ` from `r_i`. It is a
  homeomorphism, and it matches cones with cones.
- **Coset coordinate.** The lift of `β` ends at `(t(β), Γ'ℓ_β)`.
- `Γ'` acts on `Ẽ` through `ψ`.

**Step 2 (RSG).**
- Let `[β̃]` and `[β̃']` be proper cones of `Ẽ` ending at the same vertex `(u, c)`. Then `t(β) = t(β') = u` and
  `Γ'ℓ_β = Γ'ℓ_{β'}`, so `ℓ_{β'}ℓ_β^{-1} ∈ Γ'`.
- On `[β]` this element is the canonical similarity `[β] → [α_u] → [β']`.
- Its lift is the canonical similarity of the refined cones, because lifts of equal tails from equal vertices are equal.

**Step 3 (rational, finite nucleus).**
- The smallest refined cone containing `ψ(g[β])` is `ψ` of the smallest cone containing `g[β]`.
- The refined local action at `β̃` sends the lift of `ω` from `(t(β), c_β)` to the lift of `g|_β(ω)` from
  `(t(β'), c_{β'})`. So it is determined by `(g|_β, c_β, c_{β'})`.
- Hence every `g ∈ Γ'` has finitely many refined local actions, and the deep ones lie in `Nuc_G × (Γ'∖G)²`.

**Step 4 (irreducible core iff (T)).**
- **Recurrent components project into `Γ_0`.** A cycle of `Γ̃` projects to a closed walk of `Γ`, which lies in the
  unique recurrent component `Γ_0`. So every recurrent component of `Γ̃` lies over `Γ_0`.
- **Over `Γ_0`, the components are the `Λ_v`-orbits.**
  - `Γ_0` is strongly connected, so the strongly connected components of `Γ̃|_{Γ_0}` correspond to the orbits of the
    closed-walk labels at `v` acting on `Γ'∖G` by right multiplication.
  - That monoid acts on a finite set by permutations, so it is a group, namely the image of `Λ_v`.
  - Each such component contains cycles, so it is recurrent.
- **Reachability.** Every reachable recurrent component contains a reachable `(v, c)`, and the reachable `c` are the
  `Γ'ℓ_β` with `t(β) = v`.
- **Conclusion.** There is a unique reachable recurrent component iff (T) holds. By
  `sft-irreducible-core-iff-unique-recurrent-component` that is an irreducible core; its hypotheses (no isolated points,
  no empty cones) are inherited through `ψ` and through lifting of edges. This proves items 1–2.

**Step 5 (item 3).**
- If `Γ'Λ_v = G`, the right action of `Λ_v` on `Γ'∖G` is transitive, so (T) holds.
- The commensurability statement: a group commensurable with `G` contains, with finite index, a group isomorphic to a
  finite-index subgroup of `G`. Apply `contracting-rsgs-closed-under-finite-index-overgroups`. ∎

**The RACG instance.**
- In the greedy coding each step applies one generator, so a closed walk of length `p` has a label of parity `p`.
- Walks along the complement graph `𝒩` among singletons give all of `W⁺`.
- **An odd loop.** If `L` has an edge `{t,t'}`, spreadness (a) for `σ = {t,t'}` gives `s ∉ St(t) ∪ St(t')`, and then
  `{s} → {t,t'} → {max} → {s}` is a closed walk of length 3. If `L` has no edge, `𝒩` is complete on at least 3 vertices
  and has a triangle.
- So `Λ = W`.
