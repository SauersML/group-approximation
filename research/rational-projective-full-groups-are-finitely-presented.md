---
rg: 2
id: rational-projective-full-groups-are-finitely-presented
kind: claim
title: The full group of integral projective germs on the rational Cantorization of the m-sphere is finitely presented
distinct_from:
  closed-mcg-embeds-in-rational-projective-full-group: that constructs the host and proves it is full and clopen transitive with the mapping class group inside; this is the remaining finiteness statement about the host.
  train-track-trace-groupoid-hosts-closed-mcg: that phrases finite presentation (its gate G4) for a train-track trace groupoid; this is the same gate for the canonical rational Cantorization host, where gates G1–G3 are already settled.
---

**OPEN** (lane bh-free-54, 2026-09-18).

## Statement

For every `m ≥ 2` (at least for `m = 6g − 7`, `g ≥ 3`), the group
`𝒯_m = [[GL_{m+1}(Z) ⋉ Ŝ_m]]` of `closed-mcg-embeds-in-rational-projective-full-group`
is finitely presented.

## Why it matters

- With `closed-mcg-embeds-in-rational-projective-full-group`, it gives
  Boone–Higman for every closed-surface mapping class group of genus `g ≥ 3`
  (BBMZ Problem 5.3(2)), through `closed-mcg-bh-via-rational-projective-full-group`
  and `fp-clopen-transitive-full-cantor-groups-have-type-a-actions`.
- It would also give an explicit finitely presented full clopen-transitive
  Cantor group containing `SL_{m+1}(Z)`, which is relevant to the open Kazhdan
  questions about Thompson-like groups.

## What is known

- **`m = 1`:** `𝒯_1` contains `V ≅ V_{2,4}` (calibration in the proof route).
  Whether `𝒯_1` itself, which also has orientation-reversing germs, is exactly a
  Higman–Thompson-type finitely presented group is not checked here.
- **Hypotheses of the standard simplicity and finite-generation theorems** (not
  applied or read at source here):
  - Hausdorff, effective, minimal, purely infinite, with compact open generating
    set: all proved in the proof route.
  - Expansive: `GL_{m+1}(Z)` is transitive on primitive integral forms, so the
    orbit of the single clopen `H_{x_0}` generates `B_m`.
  - Hence, by Matui's and Nekrashevych's theorems, `[[𝒢]]'` should be simple and
    the alternating full group finitely generated.

## Attempts

1. **Brown's criterion, set up** (lane bh-free-54, 2026-09-18; reasoning only).
   - **The poset.** Take unimodular clopen partitions of `Ŝ_m`, labelled by
     elements of `GL_{m+1}(Z)` identifying each piece with `Δ`, and order them by
     refinement.
   - **Vertex stabilizers.** They are finite: symmetric groups on the pieces,
     times the finite stabilizer of `Δ` in `GL_{m+1}(Z)`.
   - **Directedness.** Any two unimodular fans have a common unimodular
     refinement (common refinement, then toric resolution). So the poset is
     directed and its realization is contractible.
   - **Where it differs from `V`.** In `V`, a leaf splits in exactly one way. Here
     a unimodular simplex has many elementary subdivisions, and not every
     unimodular refinement is reached through finitely many *types* of
     elementary moves. The natural finite-type choice is edge-stellar
     subdivisions at `w_i + w_j`.
   - **What the combinatorics turn on.** Two questions:
     - whether the edge-stellar refinement poset is still directed;
     - whether its descending links are highly connected.

     The first is a strong-factorization question for toric birational maps (an
     Oda-type conjecture, open in dimension ≥ 3 for cones). The weak
     factorization theorem (Włodarczyk; Abramovich–Karu–Matsuki–Włodarczyk) gives
     connectivity by stellar moves and their inverses, which is exactly what is
     needed for the one-dimensional part of such arguments.
   - **Status.** Recorded as the precise combinatorial core of the gate. Nothing
     proved.
