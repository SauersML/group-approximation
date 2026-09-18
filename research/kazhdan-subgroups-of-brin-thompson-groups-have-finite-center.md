---
rg: 2
id: kazhdan-subgroups-of-brin-thompson-groups-have-finite-center
kind: claim
title: Every subgroup of a Brin-Thompson group nV with property (T) has finite center
distinct_from:
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that asks for finiteness of every Kazhdan subgroup of nV and implies this; this asks only for finiteness of the center, which already excludes Deligne-type lattices and the Torelli lower-central quotients from every Brin-Thompson host.
  kazhdan-subgroups-of-almost-v-have-no-central-v-elements: that controls central elements of Kazhdan subgroups of almost-V; this is the analogous question for the product cubes of nV.
---

**OPEN.** For every `n ≥ 1` and every `K ≤ nV` with property (T), `Z(K)` is
finite.

**Status.**
- **n = 1:** true, because Kazhdan subgroups of V are finite
  (`thompson-v-has-haagerup-property`).
- **n ≥ 2:** open. It follows from
  `kazhdan-subgroups-of-brin-thompson-groups-are-finite`.

**What it would give** (lane observations, not reviewed):
- **The Torelli quotients.** `Q_{g,c}` (g ≥ 3, c ≥ 2) contains an infinite
  Kazhdan subgroup `E` with infinite central subgroup `D_1`
  (`torelli-lower-central-quotients-not-rf-proof`, Steps 4–6). `E` is Kazhdan
  because, modulo a finite central subgroup, it is commensurable with a finite-index
  subgroup of the Kazhdan Deligne lattice over `Sp_2g(Z)`. So `Q_{g,c}` would embed
  in no `nV`.
- **Deligne's lattices.** Each `Γ~` over `Sp_2g(Z)`, g ≥ 2, has infinite cyclic
  center, so it would embed in no `nV`.
- **Zaremsky 2.19(c)** is not reached, because `SL_3(Z)` has trivial center.

**An invariant a proof can use** (lane lemma, elementary). Let `z ∈ Z(K)` and let
`s(g,x) ∈ Z^n` be the slope (prefix-length change) cocycle of `nV` on `C^n`.
- From `gz = zg`: `s(z, gx) = s(z,x) + s(g, zx) − s(g, x)`.
- So for every `z`-invariant probability measure `μ`, the drift
  `δ(μ) = ∫ s(z, x) dμ(x) ∈ R^n` satisfies `δ(g_*μ) = δ(μ)` for all `g ∈ K`.
  The last two terms integrate to the same value, by `z`-invariance.
- `K` therefore acts on each drift level set of the compact convex set of
  `z`-invariant measures on any closed `K`-invariant set.

**What this does not give.** A Kazhdan group acting on a compact convex set need
not have a fixed point, so the lemma alone doesn't decide the claim. Combining it
with `kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures` (a
counterexample `K` has a closed invariant set `Z_K` carrying no `K`-invariant
measure) is the natural next step.

## Attempts

- 2026-09-18 (lane bh-free-38). **Periodic points of central elements.**
  `kazhdan-central-elements-of-2v-have-slope-free-periodic-points`
  (ESTABLISHED, lane proof) settles part of the question. For `z ∈ Z(K)` with `K`
  Kazhdan or FW:
  - The slope of `z^m` at its fixed points is `K`-invariant.
  - The corresponding fixed set is locally a point times a cube, and `K` acts on
    it through a lower-dimensional Brin–Thompson group.
  - Farley, plus the germ character, then rule out any nonzero slope.
  - So in 2V a counterexample to this claim needs an infinite-order central `z`
    whose periodic points all have slope zero, such as a minimal element like the
    SMART moving-tape map, or an element with no periodic points.
  - The drift lemma above then constrains such `z`, but doesn't decide the claim.
    No literature result on nilpotent or Heisenberg subgroups of nV (n ≥ 2) was
    found by a bounded arXiv search.
