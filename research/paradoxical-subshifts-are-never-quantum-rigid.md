---
rg: 2
id: paradoxical-subshifts-are-never-quantum-rigid
kind: claim
title: The Barbieri–Sablik–Salo paradoxical subshift has a finite modification at almost every vertex, so it is never quantum rigid, over any group, at any scale, over any field; nor is its trivial extension to a product
distinct_from:
  minimal-sfts-with-a-finite-modification-are-not-quantum-rigid: that kills minimal SFTs with one finitely supported modification; this applies its far-modification Lemma to a non-minimal SFT, the geometry layer of self-simulation, where a local recolouring gives modifications everywhere.
  nonamenable-products-have-minimal-sft-extensions-of-free-inputs: that is the minimal self-simulation premise (MSS) for gate E1; this shows the geometry layer of the BSS construction behind it cannot serve as the rigid base for gate E2.
  deterministic-extensions-of-rigid-sfts-are-rigid: that transports rigidity from a rigid base to deterministic layers; this shows the BSS geometry is not such a base, so its colour choices must be pinned by another layer.
---

**ESTABLISHED (lane bh-g2-fixedpoint-b, 2026-09-18; elementary lane proof, not reviewed; no priority
claimed).** Quantum families (Q1)–(Q3) and `D`-rigidity are as in
`fp-v-times-subshift-full-groups-force-quantum-rigidity`.

## Setting (Barbieri–Sablik–Salo, arXiv:2104.05141, Definition `def:paradoxical_subshift`, TeX read at source)

`Γ` is a countable group and `K ⊆ Γ` finite and symmetric. A symbol is
`a = ((L_G(a), L_B(a), R(a)), t(a))` with three entries in `K` and a colour `t(a) ∈ {G, B}`. The
**paradoxical subshift** `P_K ⊆ (A_K)^Γ` is cut out by three conditions at every `g`, with `a = ρ(g)`:
1. `b = ρ(g L_G(a))` has colour `G` and `R(b) = L_G(a)^(-1)`;
2. `c = ρ(g L_B(a))` has colour `B` and `R(c) = L_B(a)^(-1)`;
3. if `d = ρ(g R(a))` then `L_(t(a))(d) = R(a)^(-1)`.

Put `φ(g) = g R(ρ(g))`, `h_G(g) = g L_G(ρ(g))` and `h_B(g) = g L_B(ρ(g))`.
- Condition 3 at `u` with `φ(u) = g` gives `u = h_(t(u))(g)`.
- Conditions 1 and 2 give `φ(h_G(g)) = φ(h_B(g)) = g`.

So `φ` is `2`-to-`1`, and the preimages of `g` are `h_G(g)` (green) and `h_B(g)` (blue). BSS prove
`P_K ≠ ∅` for suitable `K` iff `Γ` is non-amenable. `P_K` is an SFT with forbidden patterns on `K ∪ {1}`.

## Theorem

Let `P_K ≠ ∅` and `Γ` be infinite. For every `D` and every field `k`, `P_K` is not `D`-quantum rigid
over `k`. The same holds for the trivial extension `P̃ = P_(K_H) ⊠ P_(K_V)` over `Γ_H × Γ_V`, the
geometry layer of BSS Theorem `thm:selfsimulation`.

## Proof

**Recolouring move.** Fix `ρ ∈ P_K` and a vertex `v` with `φ(v) ≠ v`. Write `h_G = h_G(v)` and
`h_B = h_B(v)`. These are distinct, since they have different colours, and neither equals `v`, since
`v` is not its own preimage. Define `ρ'` by three changes:
- at `v`, exchange `L_G` and `L_B`;
- recolour `h_G` blue;
- recolour `h_B` green.
Nothing else changes. So `Δ(ρ, ρ') ⊆ {v, h_G, h_B} ⊆ vK`, and `ρ' ≠ ρ`.

**`ρ' ∈ P_K`.** Only conditions that read a changed entry need checking.
- *Conditions 1 and 2 at `v`.* The new green arrow `L_B(v)` points to `h_B`, which is now green,
  and `R(h_B) = L_B(v)^(-1)` by the old condition 2. The blue case is symmetric.
- *Conditions 1 and 2 at `g ≠ v`.* They read the colour of `g L_G(g)` and `g L_B(g)`, the preimages
  of `g`. These are never `h_G` or `h_B`, whose image is `v`. They also read `L`-entries only at `g`,
  which is unchanged.
- *Condition 3 at `h_G`.* Its new colour is `B`, so it reads the blue arrow at `φ(h_G) = v`. That
  arrow is `L'_B(v) = L_G(v) = v^(-1) h_G = R(h_G)^(-1)`, as required. The same holds at `h_B`.
- *Condition 3 at `v`.* It reads `L_(t(v))` at `φ(v)`. Here `φ(v) ≠ v`, the colour of `v` is
  unchanged, and the `L`-entries at `φ(v)` changed only if `φ(v) = v`. So it is unchanged.
- *Condition 3 at any other `g`.* It reads `ρ(φ(g))`. If `φ(g) = v`, then `g ∈ {h_G, h_B}`, which
  was treated above. Otherwise nothing it reads changed.

**Enough movable vertices.** If `φ(v) = v`, then the other preimage `u` of `v` has `φ(u) = v ≠ u`
and `d(u, v) <= |K|`, where `|K| = max_{k∈K} |k|`. So the vertices with `φ(v) ≠ v` are
`|K|`-dense in `Γ`. Since `Γ` is infinite, there are two such vertices `v, w` with
`d(v, w) > 2D + 2|K|`.

**Conclusion.** Recolouring at `v` and at `w` gives modifications `ρ_1, ρ_2` of `ρ` whose difference
sets lie in `vK` and `wK`, which are at distance `> 2D`. The far-modification Lemma of
`minimal-sfts-with-a-finite-modification-are-not-quantum-rigid` needs no minimality. It gives a
noncommuting `D`-family on `k^2`.

**Products.** By `quantum-rigidity-is-product-stable`, item 3 (converse), rigidity of
`P_(K_H) ⊠ P_(K_V)` would force rigidity of `P_(K_H)`. ∎

## What this means for gate E2 on Track A

The self-simulation route to E1 (`minimal-free-sft-via-minimal-self-simulation-of-squares`) builds its
grids on `P̃`. The theorem does not say that the whole BSS SFT `Z` is non-rigid. A recolouring
exchanges the tails of two paths, so in `Z` it forces changes along whole grids and is no longer a
finite modification. It does say three things.
- The rigidity-transport scheme "rigid base + deterministic layers"
  (`quantum-rigidity-is-product-stable`, `deterministic-extensions-of-rigid-sfts-are-rigid`) cannot
  use BSS's geometry as its base. The colour field is a free layer.
- In a rigid `Z` the computation layer must itself forbid every recolouring. Determination then
  runs from computation to geometry, which is the opposite of what the transport theorems handle.
- The fix is a geometry whose paradoxical structure is a **deterministic function of a rigid
  layer**. `end-shift-path-covers-are-rigid-with-one-spine` gives one over every group with a direct
  factor `F_n` (`n >= 2`).

## Lesson for general BH

A paradoxical decomposition is made of local choices: which preimage is green. Local choices at far
apart places are independent, and independence at distance `> 2D` is exactly what the
far-modification certificate needs. So no geometry whose paradoxicality is a free choice is
quantum rigid. Non-amenable geometry helps rigidity only when a rigid layer, such as a boundary flow,
dictates the choices. That is the difference between the BSS subshift and the end shift of a tree,
which is paradoxical (every vertex has `2n - 1` children) and rigid.
