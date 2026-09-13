---
rg: 2
id: non-linear-sofic-via-bowen-chapman-rank-transcription
kind: route
title: Transcribe the Kun--Thom normalization proof into characteristic-two rank for the Bowen--Chapman pair
target: non-linear-sofic-group
requires: []
artifacts:
  - research/artifacts/nls-rank-metric-witness-2026-09-12.md
---

# Transcribing Kun--Thom 4.1 for the Bowen--Chapman pair

## Why sufficient

- **The consumer transfers to rank** (artifact Section 2.1).
  - Normalized rank is bi-invariant.
  - `F`-linear soficity passes to the index-two lamp extension
    `G *_Gamma (Gamma x C_2)`.
  - `lampWitness_ne_one` supplies the defect.
  - So suppose `Gamma` normalizes sequential rank almost-centralizers in every
    `F`-linear sofic approximation of `G`. Call this `NORM_F`. Then the Bowen--Chapman
    double `SymmetricDouble Ambient Peripheral` is not `F`-linear sofic. That is
    [[non-linear-sofic-group]].
- **The route.** It proves `NORM_F` for a characteristic-two `F` by transcribing
  `seqNormalizes_of_compressor_of_steps` step by step.
  - Property (T) rounds almost-invariant subspaces of approximations of `G` to
    `Gamma`-invariant pieces. This is step (K): `hdecomp`, `hdefect`.
  - It rounds almost-centralizers of `Gamma` to maps respecting those pieces
    (`hrep`).
  - Then come one-piece transport, no drift and collision, as in Kun--Thom.

## Dead

- **Rounding fails** ([[bowen-chapman-ambient-rank-models-do-not-round-peripheral]]).
  Over every characteristic-two field, some `F`-linear sofic approximations of `G`
  by homomorphisms have:
  - `O(1/N)`-almost-invariant subspaces at normalized distance at least `1/128`
    from every invariant subspace;
  - no internally expanding pieces of linear size;
  - almost-centralizers at normalized distance `1/64` from the exact commutants.

  So neither rounding step holds for approximations of `G` itself. This is not only
  a failure for models of `Gamma`.
- **One-piece transport also fails, over every field** (artifact Section 2.3). Let `G`
  act on `U (x) F^3` through `rho_U (x) B`, with
  `B : G -> EL_3(Z) -> GL_3(F)`. Some elementary compressor carries a piece
  `U (x) L_k` to a subspace with `dim U` dimensions outside every piece.
- **Not killed:**
  - `NORM_F` itself;
  - expander decompositions with pieces of sublinear dimension;
  - step (K) over fields of odd or zero characteristic.
