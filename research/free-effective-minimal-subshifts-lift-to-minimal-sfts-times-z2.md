---
rg: 2
id: free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2
kind: claim
title: Over a finitely generated group with solvable word problem, every effectively closed minimal free subshift is a plane-invariant factor of a minimal free SFT on the product with Z^2
distinct_from:
  effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts: that is (M1) for every effectively closed minimal input; this is (M1) for FREE inputs, which is the only case the P1 routes use. Freeness is exactly what lets the diversification slots tell planes apart.
  plane-coupled-floating-tuples-are-jointly-diversifiable: that asks for a design forcing the floating tuples to be Y-patterns; this leaves the floating tuples uncontrolled and realizes every one of them in slots keyed by each plane's own table, so that crux is bypassed, not proved.
  durand-romashchenko-minimal-sft-simulation: that is the Z^d theorem, where input and hierarchy share the horizontal directions and minimality needs DR's standard-alignment machinery; here they sit in commuting direct factors, and that machinery is not needed.
  nonamenable-products-have-minimal-sft-extensions-of-free-inputs: that is minimal self-simulation over a non-amenable square (BSS Question Q:minimal, restricted), still open; this uses an amenable Z^2 factor transverse to the input and makes that question unnecessary for P1.
---

**PROVED (lane proof at the level of a design, 2026-09-18, bh-g1-simulation; unreviewed).** Proof:
`keyed-diversification-slots-give-plane-constant-minimal-lifts`. It modifies the
Durand–Romashchenko construction for their Theorem 7, read at source (arXiv:1802.01461:
letter delegation §4.1, Lemma `lemma-clones-with-embedded-bits` with its corollary, Lemma
`l:sub-grid-of-clones`, Cases 1–3 of the proof, and the minimal-version Claims 1–3). No
priority is claimed.

## Statement

Let `Λ_0` be a finitely generated group with solvable word problem, and let `Y ⊆ B^{Λ_0}` be
nonempty, effectively closed, minimal and **free**. Put `Λ = Λ_0 x Z^2`. Then there are:
- a finite alphabet `A`;
- a nonempty SFT `X ⊆ A^Λ` on which `Λ` acts **minimally and freely**;
- a continuous surjection `Φ : X -> Y`,

such that:
- `Φ((λ,0)·x) = λ·Φ(x)`;
- `Φ((1,z)·x) = Φ(x)`.

This is (M1) of `effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts`, restricted to
free `Y` and strengthened with freeness of all of `Λ`.

## The two mechanisms

1. **Transverse factors remove synchronization.**
   - The input lives on `Λ_0`, constant along planes, and the hierarchy lives on `Z^2`, constant
     along `Λ_0`. So a pattern at `(λ,z)` is fixed by data at `λ` and by skeleton near `z`, and the
     two recur independently.
   - This is why DR's minimal version needs the "standard alignment" of the input with the
     macro-tile grid (their Claims 1–3: minimality fails for a periodic input whose period divides
     `L_k`), and why this construction does not.
   - It is the same reason BSS obstacle (b), synchronized return times, cannot occur between
     commuting factors.
2. **Keyed diversification kills the plane-tuple crux.**
   - Every such lift must have a floating locus (`injective-plane-lift-codings-force-finite-type`):
     content on infinite father-chains that no finite level determines. In each plane it is
     independent.
   - DR's slots show a fixed pattern per slot, so across planes they show only constant tuples.
     That is the failure recorded on the crux node.
   - Here a slot at level `K` shows `i(τ)`, where `τ` is the plane's own level-`K` table
     (`f ↦ y(λf)`, `f ∈ F_K`) and `i` ranges over all functions from tables to admissible
     window contents.
   - Freeness of `Y` makes the tables of the planes `λf`, `f ∈ F`, pairwise distinct once `F_K`
     contains a freeness radius for `F^{-1}F`. So one slot shows any prescribed tuple on any
     finite window of planes.

## Scope and limits

- **Free inputs only.** If `g·y = y` with `g ≠ 1`, then with the proof's convention
  (`(g·y)(h) = y(g^{-1}h)`, tables `f ↦ y(λf)`) the planes `λ` and `gλ` carry equal tables at
  every level. Floating content there can differ,
  and no key separates them. (M1) for non-free `Y` stays open, and P1 does not need it.
- **What `Λ_0` needs.** Only finite generation and a solvable word problem, to compute balls and
  tables. Finite presentation enters only when the lift is used for P1.
- **Rigidity is not addressed.** Quantum rigidity of `X` is gate E2. For simulations of this
  kind it is exactly `plane-constant-simulation-computation-layers-are-quantum-rigid` (RS), which
  is open. The floating locus is forced, so the lift is never boundedly determined
  (`bounded-determination-simulations-only-realize-sft-shadows`).

## Lesson for general BH

The SFT upgrade in the existence gate costs nothing. Effective minimal free dynamics on an
fp decidable group becomes a minimal free SFT one `Z^2` factor up, with two moves:
- Put input and hierarchy in commuting factors, so that return times cannot synchronize.
- Diversify the unavoidable floating content with slots keyed by each plane's own finite data.
  The input's freeness turns that data into a proper colouring of every finite window of planes,
  so no global coordination is needed.

Minimal self-simulation over non-amenable squares is then off the critical path for existence.
What remains of E1 is (M2) itself: see `minimal-free-sft-overgroups-exist-iff-m2-overgroups-exist`.
