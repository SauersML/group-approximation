---
rg: 2
id: minimal-free-sft-overgroups-exist-iff-m2-overgroups-exist
kind: claim
title: A decidable group lies in an infinite finitely presented group carrying a minimal free SFT iff it lies in a finitely presented decidable group carrying an effectively closed minimal free subshift
requires:
  - free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2
distinct_from:
  decidable-groups-embed-in-fp-groups-with-minimal-free-sft: that is (P1), the left side for all inputs; this proves it equivalent, input by input, to the right side.
  decidable-groups-embed-in-fp-groups-satisfying-m2: that is the right side for all inputs, still open; this shows it is not weaker than (P1).
  plane-constant-minimal-sft-factors-are-effective-minimal: that extracts effective minimality from a plane-invariant factor of a minimal SFT over a general group; this uses the elementary direction (a minimal free SFT is itself an effective minimal free subshift) plus Jeandel, and adds the converse.
---

**PROVED (lane proof, 2026-09-18, bh-g1-simulation; unreviewed).** The converse direction rests
on `free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2`, a design-level proof.

## Statement

Let `K` be a finitely generated group with solvable word problem. The following are equivalent.
- **(A)** There is an infinite finitely presented `Λ ⊇ K` carrying a nonempty minimal free SFT.
- **(B)** There is a finitely presented `Λ_0 ⊇ K` with solvable word problem carrying a nonempty
  effectively closed minimal free subshift.

Hence (P1) `decidable-groups-embed-in-fp-groups-with-minimal-free-sft` is equivalent to
`decidable-groups-embed-in-fp-groups-satisfying-m2`.

## Proof

**(A) ⇒ (B).** Take `Λ_0 = Λ`.
- An SFT is effectively closed.
- A nonempty free SFT is strongly aperiodic. So `Λ` has solvable word problem by Jeandel,
  arXiv:1501.06831, read at source, abstract: "If a finitely presented group G admits a strongly
  aperiodic SFT, then G has decidable word problem."

**(B) ⇒ (A).** Let `Y` be the subshift on `Λ_0`. Put `Λ = Λ_0 x Z^2`.
- `Λ` is finitely presented, infinite, and contains `K`.
- By `free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2`, `Λ` carries a nonempty
  minimal SFT on which it acts freely. `∎`

## What this says about gate E1

- **The SFT condition is free.** Given the overgroup, the existence side of the master route (P1)
  is exactly effective minimal free dynamics (M2). No minimal self-simulation is needed, whether
  BSS Q:minimal over `Λ_1 x Λ_1` or the plane-tuple crux.
- **Simulation cannot produce (M2).** Every minimal free SFT already is an (M2) instance. So (M2)
  is the irreducible content of E1, not an artifact of the chosen route.
- **Where the wall is.** For simple Kazhdan inputs this is the central→global recurrence wall of
  `decidable-fp-groups-have-effective-minimal-free-subshifts` (Attempts 2–8). The live attack is
  `decidable-groups-have-universal-hyperaperiodic-points` via
  `m2-envelopes-via-free-product-with-z`.
- **Self-simulation.** Self-simulability of the envelope can always be arranged: `Λ_1 x F_2` is
  a product of non-amenable groups, so it is self-simulable by BSS Theorem `thm:selfsimulation`.
  But it is no longer used.

## Lesson for general BH

In the existence gate, the only hard object is an effectively closed minimal free subshift on an
fp decidable overgroup. Finite type is then free, one commuting `Z^2` factor up. Work on E1 should
target (M2) directly, that is, free minimal dynamics with a computable global recurrence modulus
and no profinite skeleton. Gate E2 (rigidity of the lift) is separate.
