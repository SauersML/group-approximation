---
rg: 2
id: beta-hinted-crossing-wire-shifts-are-free-minimal-rigid-proof
kind: route
title: Hint fields sit on every edge and are constant, so they are central exactly as coordinates are; the β-check is one more deterministic zone task; DR minimality runs with the hint as a global constant
target: beta-hinted-crossing-wire-shifts-are-free-minimal-rigid
requires:
  - minimal-crossing-wire-fixed-point-shift-is-quantum-rigid
  - crossing-wire-fixed-point-tile-sets-are-quantum-rigid
  - fixed-point-wang-tile-rigidity-is-edge-family-commutation
---

Lane proof (swarm-0917-w18c-w18c-bh-pull, 2026-09-19). Not independently reviewed. "Parent proof" means
`minimal-crossing-wire-fixed-point-shift-is-quantum-rigid-proof` (parts A1–A4, B, C). "Base proof" means
`crossing-wire-fixed-point-tile-sets-are-quantum-rigid-proof` (Steps 1–5). DR is arXiv:1802.01461.

## H1. The program still fits (existence, item 1, item 5(a))

- **Colour length.** A `τ_k`-colour gains `2k + 3` hint bits. DR's colour length is
  `k_r = Θ(log N_(k+1)) = Θ(C^(k+1))`, which dominates `k`. So the colour stays `O(log N_(k+1))`
  and every room estimate of the parent proof ("Room", part B) is unchanged up to constants.
- **Zone time.** Checks 1–2 are `O(k_r)` comparisons. Check 3 runs `B` for `m_(k+1) = poly(log N_(k+1))`
  steps, the zone's own budget. So the zone's computation is still `poly(log N_(k+1))` and
  deterministic, as (p2) of DR and (L4) require.
- **Fixed point.** The program that DR's fixed-point step (§2.3–2.4) reproduces is DR's program plus
  the text of `B` and checks 1–3, a constant-size addition. Their argument needs only that the zone can
  compute the rules of `τ_(k+1)` from the rank and the program in the zone budget for all `k >= 0`
  (increase `C` if necessary). As in the parent, this is recalled, not re-verified line by line.
- **The β-hinted hierarchy exists.** Put the pair `(β|(k+1), β|(k+2))` on every `τ_k`-tile at every
  level, and build the DR hierarchy. Check 1 holds. Check 2 holds: for a `τ_k`-tile `t` with father
  `f ∈ τ_(k+1)`, the first word of `f` is `β|(k+2)`, and so is the second word of `t`, so the bit `f`
  sends on its wire `i` is `t`'s `g'_i`. Check 3 holds because
  every computed `β_j` is correct. So DR's existence argument yields a tiling. Hence `Ω_β ≠ ∅`.
- **Exact simulation (5(a)).** DRS simulation is a bijection between accepted `τ_(k+1)`-tiles and
  valid level-`k` macrotiles (Durand–Romashchenko–Shen, *Fixed-point tile sets and their
  applications*, JCSS 2012, the definition of "simulates"); DR's variable zoom keeps it. So `M(t)` is
  unique. Build it top-down: expand `t` into its `N_k × N_k` children (the layout is `poly(log N_k)`
  computable from coordinates and inputs, the zone is run deterministically), and recurse. Total time
  `poly(L_k)`. If some zone at some level rejects, the expansion stops and reports it.
- **Size.** `L_k = N_1 ⋯ N_k = 3^(C + C^2 + … + C^k) <= 3^(C^(k+1))`.

## H2. Every tiling carries β (item 1)

Let `x ∈ Ω_β`. By DR §2 (unchanged), for every `k`, `x` has a unique decomposition into level-`k`
macrotiles, each representing a `τ_k`-tile, and each level-`k` macrotile is a child of a level-`(k+1)`
one.

1. *Constancy per level.* All `τ_k`-tiles of the level-`k` grid of `x` carry one pair `(h_k, h'_k)`:
   the tile rule makes the pair the same on four sides, and neighbours share a side.
2. *Levels agree.* `h_k` is a prefix of `h'_k` (check 1). Some `τ_k`-tile lies on its father's wire
   for bit `i` of the father's first word, for each `i < k + 2`, and that wire carries `h_(k+1),i`.
   Check 2 gives `h_(k+1),i = h'_(k,i)`. So `h'_k = h_(k+1)`. Hence there is one infinite word `y` with
   `h_k = y|(k+1)` and `h'_k = y|(k+2)` for all `k`.
3. *`y = β`.* Fix `j`. `B` computes `β_0, …, β_j` in some finite number `s_j` of steps. Choose `k`
   with `m_(k+1) >= s_j` and `k + 3 > j`. Every `τ_(k+1)`-tile of `x` passed check 3, so `y_j = β_j`.

## H3. Minimality (item 3)

Follow part B of the parent proof. Let `w` be a 2×2 block of rank-`k` macrotiles in `x`. By H2, all
hint fields in `w` and in every other tiling are the same, namely `β`-prefixes.
- **Case 1 (skeleton).** The hint fields of skeleton tiles are the global constants. So a skeleton
  window is still a function of its coordinates in every tiling, and recurs at the homologous
  position of every rank-`(k+1)` macrotile.
- **Case 2 (one wire).** If the wire carries a hint bit, its value is the global constant `β_s`. The
  window is then a function of coordinates, as in Case 1, and recurs at the homologous position. If it
  carries a non-hint bit, DR's property (p4) applies unchanged. (p4) is a property of the non-hint
  macro-colour bits: coordinates in the father and DR's rank and program bits. The hint fields are not
  involved.
- **Case 3 (zone, crossing, fan-out).** `w` is 2×2-determinate as before. Its hint fields are the global
  constants, so its filling is among those enumerated by (H-slot) in every rank-`(k+1)` macrotile.
  The slot reproduces it, with fake coordinates equal to the real ones. This is exactly DR's
  argument. The only change is the filter "hint = own hint". A filling whose hint differs never
  occurs in any tiling, by H2, so nothing is lost.
- **Case 4 (slot, frame).** A slot's frame colours are functions of the frame's real coordinates and of
  the macrotile's hint pair, which is the global constant. So Case 4 is unchanged.
- **Realizability of slot contents.** The enumerated fillings are realized inside the slot itself. Each
  of their tiles has an accepted pair, since its hint is the true `β`-prefix pair, so it expands by
  H1.

So every pattern of every tiling occurs in every rank-`(k+2)` macrotile of every tiling, and `Ω_β` is
minimal.

**Freeness (item 2)** is DR §2 (DRS Prop. 1), unchanged: the hierarchy forces every period to be a
multiple of every `N_1 ⋯ N_k`.

## H4. Rigidity (item 4)

By item 1 of `fixed-point-wang-tile-rigidity-is-edge-family-commutation`, it is enough that every
face-local edge family (FLEF) `P` of `τ^β_0` commutes. Run the parent proof, with one addition to Step 1
of the base proof.

**Step 1′ (hint fields are central).** For a face `z` and a pair `a`, let `H_a(z)` be the projection
"face `z` carries hint pair `a`". The pair is part of the colour of each edge of `z`. Let `H_a(e)` be the
sum of the colour projections of edge `e` whose hint part is `a`. For two edges `e, e'` of `z` and `a ≠ b`,
`H_a(e)H_b(e')` is a sum of products of the four edge projections of `z` over colourings that are not
tiles, so it vanishes by (F2). With (F1) this gives `H_a(e) = H_a(e)H_a(e') = H_a(e')`. So
`H_a(z) := H_a(e)` lies in the algebra of each single edge of `z`, just as `C_p(z)` does in Step 1. The right edge of `z` is the left
edge of `z + e_1`, so `H_a(z) = H_a(z + e_1)`, and the same holds vertically. So `H_a(z) = H_a(z')` for
all faces, one PVM `H`. It lies in the algebra of every edge, so it commutes with every edge and is
central. The only change from Step 1 is that the index is constant instead of incrementing. Split `W`
along `H` too. On each summand the level-0 hint pair is a scalar.

**Higher levels.** Step 3 ("Centrality") applies Step 1 to `P^K`. Apply Step 1′ to `P^K` as well: the
level-`K` hint pair is part of every `P^K` side colour. So on each summand of Step 4, the hint pairs of
levels `0, …, K − 1` are scalars, alongside the coordinates.

**Everything else is as before.**
- *Steps 2–5.* Hint bits of a macrotile are input bits on wires (H-wire). They commute with the other
  inputs by (L3) crossing (Step 2(a)). The zone's checks 1–3 are deterministic functions of the inputs,
  the rank and the coordinates, so Step 2(c) applies verbatim. A1 of the parent proof ("Steps 1–5 never use
  that the tile set at level k is the same as at level 0") covers the modified program.
- *Slots (A2–A3).* The frame colours facing a slot are functions of the frame's real coordinates and of
  the hint pair. Both are scalars on each summand of Step 1 and Step 1′. So the eight outer edges of a
  slot are scalars, and A3's induction makes the inner ones scalars. Slots are still classical.
- *One-way zones (A4)* are unaffected.

So every FLEF commutes. By the target's item 4, via
`fixed-point-wang-tile-rigidity-is-edge-family-commutation` and
`sft-crossed-product-fp-iff-quantum-rigid`, `LC(Ω_β, k) ⋊ Z^2` is finitely presented over every field.
The proof uses only idempotents, sums and finite central decompositions, so it is field independent.

## H5. Placement and the corner tile (items 5(b), 5(c))

- **5(b).** Let `M(t)` occur in `x` at offset `v`. Induct on levels `j <= k`. The `τ_0`-tiles of the
  occurrence carry level-1 coordinates, and these must equal those of `x`'s level-1 grid (Step 1 of the
  classical shadow: coordinates increment across every edge). So `v` puts the level-1 blocks of `M(t)` on
  level-1 blocks of `x`. By exact simulation each such block is the macrotile of the `τ_1`-tile it
  encodes, which carries level-2 coordinates. Repeat up to level `k`: the `N_k × N_k` level-`(k−1)`
  blocks of `M(t)` carry all coordinates `0, …, N_k − 1` of one father. So the occurrence is exactly one
  level-`k` macrotile of `x`, and by exact simulation it represents `t`.
- **5(c).** Every tiling has level-`(k+1)` macrotiles. Their child at position `(0, 0)` is off every wire
  and zone (DR layout: margins and cables start at distance `>= m` from the corner, (p1)). Its colour is
  therefore determined by its coordinates, its rank and its hint pair, which is `(β|(k+1), β|(k+2))` by
  H2. So it is `c_k(β|(k+1), β|(k+2))`, and its macrotile is `M(c_k(…))`.
- **The criterion.** If `b = β_(k+1)`, `M(c_k(β|(k+1), β|(k+1)b))` occurs in every tiling (5(c)). If
  `b ≠ β_(k+1)`, then either some zone of `M(c_k(…))` rejects, so the expansion fails and the pattern is
  not locally admissible, or the expansion succeeds and the pattern cannot occur, since by 5(b) and H2 its
  occurrence would carry a wrong hint. QED
