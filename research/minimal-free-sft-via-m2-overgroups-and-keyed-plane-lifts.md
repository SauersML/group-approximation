---
rg: 2
id: minimal-free-sft-via-m2-overgroups-and-keyed-plane-lifts
kind: route
title: An fp decidable overgroup carrying an effective minimal free subshift, times Z^2, carries a minimal free SFT, by keyed plane-constant lifting
target: decidable-groups-embed-in-fp-groups-with-minimal-free-sft
requires:
  - decidable-groups-embed-in-fp-groups-satisfying-m2
  - free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2
---

**Route. OPEN in exactly one premise:** `decidable-groups-embed-in-fp-groups-satisfying-m2`.
The other premise is a design-level lane proof (bh-g1-simulation, 2026-09-18; unreviewed).

## Argument

Let `K` be finitely generated with solvable word problem.
1. The open premise gives a finitely presented `Λ_0 ⊇ K` with solvable word problem, and a
   nonempty effectively closed minimal free subshift `Y` on `Λ_0`.
2. Put `Λ = Λ_0 x Z^2`. It is infinite, finitely presented, and contains `K`.
3. `free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2` gives a nonempty minimal SFT
   on `Λ` on which `Λ` acts freely. `∎`

## Relation to the other P1 routes

- **`minimal-free-sft-via-plane-constant-minimal-simulation`.** Same shape, but it needs (M1)
  for all effective minimal inputs and (M2) for every fp envelope. Here only free inputs and one
  envelope per input are needed.
- **`minimal-free-sft-via-minimal-self-simulation-of-squares`.** Needs BSS Q:minimal (restricted)
  over `Λ_1 x Λ_1`, which is still open. This route does not.
- **Converse.** The premise is also necessary: see
  `minimal-free-sft-overgroups-exist-iff-m2-overgroups-exist`. So this route loses nothing.
