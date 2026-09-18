---
rg: 2
id: plane-local-freedom-kills-rigidity-of-plane-lifts
kind: claim
title: A lift over Λ_0 x H whose undetermined data is plane-local is quantum rigid only if all its free planes cluster; minimal lifts of non-SFT inputs must have free planes, so the keyed-slot E1 lift needs its floating data coupled across planes before gate E2 can hold
requires:
  - minimal-sfts-with-a-finite-modification-are-not-quantum-rigid
  - strongly-proximal-geometries-are-disjoint-from-measured-inputs
distinct_from:
  cross-layer-separable-modifications-kill-quantum-rigidity: that kills fibre products whose layers' modification sets separate; this is the plane-indexed case, where a single layer is split into independent planes by the absence of cross-plane rules, and it applies to the minimal E1 lift.
  keyed-diversification-slots-give-plane-constant-minimal-lifts: that builds the minimal lift, deliberately comparing only table carriers across planes; this shows that this very feature is what gate E2 must undo.
  extension-rigidity-is-base-centrality-plus-pointwise-rigidity: that decomposes E2 for layered SFTs; Part 3 here applies it to the repaired lift, and names the three residual checks.
---

**Status.** Parts 1 and 2 are ESTABLISHED (lane proofs, elementary, unreviewed). Part 3 is
design-level. Part 4 is OPEN.

**Setting.**
- `Λ_0` is infinite and finitely generated, and `H` is finitely generated.
- `Z ⊆ A^{Λ_0 x H}` is an SFT whose rules have radius `≤ D`.
- The alphabet splits into *global* coordinates and *plane-local* coordinates. No rule
  compares plane-local coordinates at sites in different planes `{λ} x H`.
- For a point `z`, let `F_λ(z)` be the set of plane-local fillings of plane `λ` that are valid
  with the global coordinates of `z` fixed.

## Part 1. Plane-local freedom is a product, and far freedom kills rigidity

**Lemma 1.** With the global coordinates of `z` fixed, the valid points are exactly
`∏_λ F_λ(z)`.

*Proof.*
- Every rule either involves global coordinates only, or involves plane-local coordinates of a
  single plane together with global ones.
- So the choices in different planes are independent. ∎

**Theorem 1.** Suppose some point `z` has `|F_λ(z)| ≥ 2` and `|F_{λ'}(z)| ≥ 2` for two planes
with `d(λ, λ') > 2D`. Then `Z` is not `D`-quantum rigid, over any field.

*Proof.*
- Changing plane `λ` alone gives a point `z_1`, and changing plane `λ'` alone gives `z_2`
  (Lemma 1).
- `Δ(z, z_1) ⊆ {λ} x H` and `Δ(z, z_2) ⊆ {λ'} x H`, which are at distance `> 2D`.
- The far-modification lemma of `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid`
  applies. As item 3 of `cross-layer-separable-modifications-kill-quantum-rigidity` records, it
  needs no finiteness of the difference sets. ∎

So a `D`-rigid `Z` of this form has **clustered freedom**: for every point, the free planes lie
in a set of diameter `≤ 2D`.

## Part 2. Minimal lifts must have free planes

**Theorem 2.** Suppose, in addition to the Setting:
- `Z` is minimal;
- `Z` has a `Λ_0`-invariant factor `τ` (the skeleton);
- `Z` has an `H`-invariant factor `φ : Z -> Y` onto a non-SFT minimal `Λ_0`-subshift;
- the global coordinates are continuous functions of `(τ, φ)`.

Then some point has a free plane.

*Proof.*
- If no point had a free plane, every point would be determined by its global coordinates,
  hence by `(τ, φ)`.
- Theorem 3(iii) of `strongly-proximal-geometries-are-disjoint-from-measured-inputs` would then
  make `Y` a subshift of finite type. ∎

**Corollary (input side).** In the E1 route, `Y = Y_1` lives on `A' = (Λ_1 x Z) * Z`. That
group has infinitely many ends, so by Cohen it carries no strongly aperiodic SFT. `Y_1` is free
and minimal, so it is not of finite type, and Theorem 2 applies.

## Part 3. The keyed-slot lift as built (design level)

In `keyed-diversification-slots-give-plane-constant-minimal-lifts` (695a89096):
- "only the twin rule refers to another plane, and it involves table carriers only";
- the skeleton is `Λ_0`-constant, and tables are determined by the letters (its step 2).

So the Setting holds, with global coordinates = skeleton, letters and tables, and
plane-local coordinates = computation, wire, border and slot data. By Theorem 2, free planes
exist.

**Expected (not proved).** At a skeleton point with an infinite computation zone, the free data
is the visible window of an infinite-level space-time diagram and the floating identities. Its
options are expected to number at least 2 for every table, not only for exceptional ones. If so:
- every plane is free at such points;
- Theorem 1 kills `D`-rigidity for every `D`.

**What would rescue the unmodified design.** Freedom only for tables in a set `Bad` whose
return-time set `{λ : λ^{-1}y ∈ Bad}` has bounded diameter for every `y`. Minimality of `Y`
makes that implausible unless `Bad` is very thin (nowhere dense).

**Design rule for E2 (WITHDRAWN 2026-09-18 by `e2-for-plane-lifts-is-clustered-floating-freedom`, Theorem C: transport-coupled lifts are rigid but never minimal for a non-SFT input).** The floating data must be *coupled across planes* so that no
modification is plane-local:
- impose a cross-plane transport `σ_{λs} = β_s(T_λ, T_{λs}, σ_λ)` on floating identities, with
  each `β_s` a bijection of admissible sets;
- restrict the keyed slots to maps `i` that are `β`-consistent.

Then:
- **Modifications become plane-global.** Changing one plane's floating data forces a change in
  every plane.
- **Theorem 2 is still respected.** Theorem 3(iii) applies only when the point is determined by
  a `Λ_0`-invariant factor together with `y`. Here the extra datum is a choice at one plane, and
  that choice moves under `Λ_0`.
- **Minimality should survive.** Keys are pairwise distinct by freeness, so every `β`-consistent
  tuple is realized by some slot. This is a sketch, not re-proved.

## Part 4. What E2 then needs (OPEN)

By `extension-rigidity-is-base-centrality-plus-pointwise-rigidity`, take the skeleton as base
and the rest as fibre. Three checks remain:
- **(a) Skeleton.** A deterministic, crossing-wire DRS skeleton is rigid
  (`crossing-wire-fixed-point-tile-sets-are-quantum-rigid`).
  - It needs points with at most one infinite zone, or nested ones. Otherwise the antipodal
    clash of `cross-layer-separable-modifications-kill-quantum-rigidity` returns.
- **(b) Relative rigidity at generic skeleton points (heuristic).**
  - The twin and zone rules make every table bit an exact operator copy of a letter idempotent
    of a nearby plane, as in `copy-constraints-make-simulation-skeleton-and-data-commute`.
  - Planes `λ` and `λf` have their copies cross in every zone of level `k` with `f ∈ F_k`,
    under the (L3) layout. So letter idempotents of *all* pairs of planes would commute.
  - The copying chains are long but consist of radius-`D` identities. So this is the
    crossing-wire mechanism transported along `Λ_0`.
- **(c) Remaining pieces.** Centrality (C) of skeleton idempotents, and rigidity of the
  `β`-coupled floating layer at infinite-chain skeleton points.

## Lesson for general BH

The feature that made E1 easy, planes that choose their floating data independently, is
exactly what E2 forbids.
- Independence across planes lets two far planes be modified separately, and the
  far-modification lemma then kills rigidity.
- Minimality forces some such freedom to exist (Part 2).
- So the E1 → E2 passage has one design obligation: couple the floating data across planes by
  bijective transports, so that every modification is plane-global.

After that, E2 on the E1 overgroup splits into:
- crossing-wire rigidity of the skeleton;
- crossing of copied table wires, which makes the letters of all planes commute (heuristic);
- centrality.

None of these involves the complexity of the input.
