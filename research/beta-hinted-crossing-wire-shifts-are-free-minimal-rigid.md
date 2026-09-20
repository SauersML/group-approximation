---
rg: 2
id: beta-hinted-crossing-wire-shifts-are-free-minimal-rigid
kind: claim
title: For every recursive 0-1 sequence β, the minimal crossing-wire fixed-point shift with plane-constant β-prefix hint fields is free, minimal and quantum rigid, and every tiling carries β at every level
distinct_from:
  minimal-crossing-wire-fixed-point-shift-is-quantum-rigid: that is the empty-payload DR crossing-wire shift; this adds plane-constant hint fields and a deterministic β-prefix check to every zone, and shows the proof survives because constant fields are central exactly like coordinates.
  plane-constant-simulation-computation-layers-are-quantum-rigid: that asks for rigidity of a payload layer simulating an effective shift (gate G1(h)); this carries no simulated shift, only one globally constant sequence, and so needs no payload gate.
  e2-for-plane-lifts-is-clustered-floating-freedom: that concerns plane-constant letters of lifts over Λ_0 x Z^2 and shows transport-coupled data of a non-SFT input is never minimal; here the group is Z^2 alone and the constant datum is a single point β, which is recursive and checked, so its no-go does not apply.
  crossing-wire-fixed-point-tile-sets-are-quantum-rigid: that is the general (L0)–(L4) theorem; this is one more instance, for a variable-zoom program with an extra constant input field.
---

**ESTABLISHED (lane proof, swarm-0917-w18c-w18c-bh-pull, 2026-09-19; unreviewed)** through
`beta-hinted-crossing-wire-shifts-are-free-minimal-rigid-proof`. It inherits the layout conditions
(R1–R3 and "existence recalled, not re-verified line by line") of
`minimal-crossing-wire-fixed-point-shift-is-quantum-rigid`, and adds the three design checks H1–H3 of
the proof. A referee should re-check H3 (minimality) first.

## The construction `τ^β`

Fix a Turing machine `B` computing a total `β : N -> {0,1}`. Start from the tile sets
`τ_0, τ_1, …` of `minimal-crossing-wire-fixed-point-shift-is-quantum-rigid` (DR variable zoom
`N_k = 3^(C^k)`, modifications (M1)–(M3)). Change them as follows.

- **(H-field) Hint fields.** Every tile of `τ_k` carries, as part of the colour of *each of its four
  sides*, a pair `(h, h')` of binary words with `|h| = k + 1` and `|h'| = k + 2`. The tile rule
  requires the four sides to carry the same pair.
- **(H-wire) Hint on wires.** In the level-`k` macrotile that represents a `τ_(k+1)`-tile, the bits of
  its pair `(h_(k+1), h'_(k+1))` are macro-colour bits like all others. They travel on wires, are fanned out
  and cross every other input wire as in (M1), and enter the zone.
- **(H-zone) Zone checks.** The zone of a macrotile representing a `τ_(k+1)`-tile `t` with pair
  `(g, g')` accepts iff all of the DR checks pass and in addition:
  1. the four sides of `t` carry the same `(g, g')`, and `g` is a prefix of `g'`;
  2. **parent consistency.** If the coordinates of `t` (its position in its father, a
     `τ_(k+2)`-tile) put `t` on the father's wire for bit `i` of the father's first hint word, then the
     wire bit that `t` carries equals `g'_i`. This compares input fields of `t` with each other, using
     `t`'s coordinates. For `τ_0` the same condition is a plain tile rule.
  3. **β-check.** Run `B` for `m_(k+1)` steps in total, where `m_(k+1)` is the zone size, on inputs
     `0, 1, 2, …` in turn. Reject iff some computed value `β_j` with `j < |g'|` differs from `g'_j`.

  All three are deterministic computations on the macrotile's input bits, the rank and the coordinates.
- **(H-slot) Slots.** The diversification slots of (M2) and DR §3.2 are enumerated over the locally
  valid fillings **whose hint fields equal the macrotile's own `(h, h')`**. Every tile of a slot carries
  that pair on its sides, like every other tile.

Let `Ω_β` be the tiling shift of `τ^β_0`. The only hint visible to `τ_0`-tiles is the pair of lengths
`1, 2`. The longer prefixes live on the wires of the higher macrotiles.

## Theorem

1. **Nonempty and hinted.** `Ω_β ≠ ∅`. In every tiling, for every `k`, every level-`k` macrotile
   represents a `τ_k`-tile with pair `(β|(k+1), β|(k+2))`.
2. **Free.** Every period of a tiling is divisible by every `N_1 ⋯ N_k`.
3. **Minimal.**
4. **Quantum rigid.** Every face-local edge family of `τ^β_0` commutes. So `Ω_β` is `D`-quantum rigid
   for every `D >= 1` over every field, and `LC(Ω_β, k) ⋊ Z^2` is finitely presented for every field
   `k`, in particular over `F_2`.
5. **Structure used for hardness.**
   - (a) *Exact simulation.* Every `τ_k`-tile `t` accepted by its zone has exactly one level-`k`
     macrotile `M(t)`, an `L_k × L_k` pattern of `τ_0`-tiles with `L_k = N_1 ⋯ N_k <= 3^(C^(k+1))`.
     Given `t`, `M(t)` is computable in time `poly(L_k)`, and the computation detects rejection by a
     zone of some level `<= k`.
   - (b) *Rigid placement.* In every tiling, every occurrence of `M(t)` is a level-`k` macrotile of that
     tiling, representing `t`.
   - (c) *Corner tile.* Let `c_k(g, g')` be the `τ_k`-tile at position `(0, 0)` of its father (off every
     wire and zone) with pair `(g, g')`. Then `M(c_k(β|(k+1), β|(k+2)))` occurs in every tiling.

Items 1, 5(b), 5(c) with the zone check give, for every `b ∈ {0,1}`:
`M(c_k(β|(k+1), β|(k+1)·b))` is a globally admissible pattern iff `b = β_(k+1)`.

## Why it matters

With `β` diagonal against a time bound, this is the hard rigid SFT that
`hard-quantum-rigid-free-minimal-z2-sfts-exist` asks for (route
`hard-rigid-z2-sfts-via-diagonal-hint-sequences`). It avoids the payload gate G1(h): the only
non-skeleton information that is constant over the plane is `β`, and constant fields are central.

DERIVATION
beta-hinted-crossing-wire-shifts-are-free-minimal-rigid-proof
