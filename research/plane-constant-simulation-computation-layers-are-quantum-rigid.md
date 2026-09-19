---
rg: 2
id: plane-constant-simulation-computation-layers-are-quantum-rigid
kind: claim
title: Some plane-constant simulation scheme for (M1) has a quantum-rigid computation layer, so the simulating SFT itself is quantum rigid
distinct_from:
  effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts: that asks only for existence of the simulating minimal SFT (M1); this asks that the simulation be quantum rigid, which (M1) does not give (golden-silver is minimal, free, of finite type and not rigid).
  free-minimal-z2-sft-is-quantum-rigid: that is the Z^2 case of G2 with no simulated data; this is G2 for simulations over Λ_0 x Z^2, reduced by the two required nodes to the computation layer alone.
  wall-rigid-z2-sft-is-quantum-rigid: that is the local-to-global step for a Z^2 SFT; this is its analogue for the computation layer of a simulation, where by the required nodes every possible non-commutativity lives.
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `copy-constraints-make-simulation-skeleton-and-data-commute`, `bounded-determination-simulations-only-realize-sft-shadows`.

**OPEN.** Gate G1(h) ("rigid simulation theorem") of
`research/artifacts/gq-bh-synthesis-master-route.md`, in reduced form. Lane bh-g1-rigidsim.

**Statement (RS).** There is a simulation scheme with the following properties. For every infinite
finitely presented `Λ_0` with solvable word problem, and every effectively closed minimal
`Y ⊆ B^(Λ_0)`, it produces an SFT `X` over `Λ_0 x Z^2` witnessing (M1)
(`effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts`) that satisfies:
- alignment (Al), copying (Cp), a rigid skeleton (R1) and uniform reading (R2), all as in
  `copy-constraints-make-simulation-skeleton-and-data-commute`;
- for all large `D` and every field `k`, the computation-layer projections `C_c(q)` pairwise commute
  in every `D`-quantum family.

**Why this is the whole of G1(h).**
- By `copy-constraints-make-simulation-skeleton-and-data-commute`, skeleton and data projections
  always commute, and every full idempotent is a product of commuting layer projections at its site.
- So (RS) is equivalent to `X` being `D`-quantum rigid over `k`.
- With (M1), (M2), and freeness from the free data factor (route
  `minimal-free-sft-via-plane-constant-minimal-simulation`), (RS) delivers the object (E): a free
  minimal quantum-rigid SFT over `Λ_0 x Z^2` for every decidable envelope.
- The growth of `Λ_0` plays no role in the reduction.

**What any solution must look like** (from `bounded-determination-simulations-only-realize-sft-shadows`):
1. **Forced ambiguity.** The computation layer is never determined by skeleton and data: there are
   configurations `x ≠ x'` with equal skeleton and data layers. So (RS) is never a formal consequence
   of (R1); the rigidity must be proved for this undetermined data.
2. **Unsplittable ambiguity (necessary).** Suppose some `x` has ambiguity modifications `x^1, x^2`
   supported on sets at distance `> 2D`. Then `X` is not `D`-rigid. A solution must rule this out at
   every large scale, in the `Λ_0`-directions as well as in `Z^2`.
3. **Heuristic, not proved: ambiguity must depend on the data.** An ambiguous parameter that is the
   same in every plane is a candidate for the aligned skeleton layer. Merging it into `H` would make
   the computation layer determined, contradicting item 1, unless the enlarged skeleton subshift is
   no longer of finite type. So the forced ambiguity has to vary with `y`, and couplings between
   planes must prevent it from being chosen plane by plane. Otherwise the kill test fires along
   `Λ_0`.

**First tests, in order.**
- (a) *Calibration.* Take the Durand–Romashchenko simulation for `Λ_0 = Z`, with `Z`-data on
  `Z x Z^2` (a variant of Hochman / Aubrun–Sablik / DR). Locate its forced ambiguity pairs, which
  should be infinite-level macrotile data at fault configurations, and apply the kill test.
  - If the ambiguity is splittable, DR-type simulations are never rigid, and a new "fault-coupled"
    design is needed.
  - If not, attempt the local-to-global step.
- (b) *Level induction.* The level induction in Conjecture G2-fp (`board/SYNTHESIS.md` v2.1) must
  handle exactly the undetermined infinite-level data. The finite levels are determined, and there
  the commutation follows from the polynomial formula in item 2 of
  `bounded-determination-simulations-only-realize-sft-shadows`, applied level by level.
  The level-by-level part of (b) is a heuristic reading, not a proved step.

**Lesson for general BH.** For the simulation route, "does coupling preserve rigidity?" has an exact
answer: coupling along `Λ_0` is always rigid, while the computation layer is never automatically so.
The master route's G2 over any envelope is therefore one question about how a computing hierarchy
stores the information its skeleton and data do not determine: it must be coupled everywhere and
never split into independent far-apart pieces.
