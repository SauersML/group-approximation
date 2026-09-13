# Boone--Higman for closed-surface mapping class groups: hosts and obstructions (2026-09-12)

**Lane:** bh-mcg-closed-surface.

**Target:** `closed-surface-mapping-class-groups-satisfy-boone-higman`, which
asks whether `Mod(S_g)`, `g ≥ 3`, embeds in a finitely presented simple group.

## 1. Live embedding premises

At main d71ae9349 the only live embedding premise is
`closed-mcgs-virtually-embed-in-punctured-mcgs`. It is consumed by route
`closed-mcg-bh-via-punctured-mcg-host`, together with:
- `punctured-surface-mcgs-satisfy-permutational-boone-higman`, which imports BFFHZ
  Corollary B;
- `boone-higman-type-a-class-closed-under-finite-extensions`.

The Birman-sequence inputs are:
- `birman-exact-sequence-does-not-virtually-split`: Chen--Salter Theorem A,
  `g ≥ 4`;
- `birman-sequence-genus-three-does-not-virtually-split`: on main, reviewed PASS.

## 2. Literature status

Belk--Bleak--Matucci--Zaremsky, survey arXiv:2306.16356v3, Remark 5.4, verbatim:
"Item (2) remains open for mapping class groups of closed surfaces of genus 3 or
greater". The arXiv search listing for "Boone-Higman", read on MSI through the
newest entry 2609.01868, shows no closed-surface result. The case stays OPEN.

## 3. Landed in this lane

| node | kind | content |
|---|---|---|
| `cantor-punctured-birman-sections-have-no-finite-end-orbit` | claim | a section of `Mod(Σ, E) → Mod(Σ)` over a finite-index subgroup has no finite orbit on `E` |
| `cantor-punctured-birman-section-orbit-proof` | route | a finite orbit gives a finite-index point stabilizer; forgetting `E ∖ {x}` splits the Birman sequence over it |
| `closed-mcg-pair-orbit-finite-actions-have-large-stabilizers` | claim | with finitely many pair orbits, stabilizers on infinite orbits are not finite, not normal, fix no multicurve and are not virtually cyclic |
| `closed-mcg-pair-orbit-stabilizer-proof` | route | bi-invariant intersection numbers `i(M, fM)` and `i(λ+, fλ+)·i(λ−, fλ−)` grow along twist powers |

### 3a. The finite-orbit obstruction

`E ⊂ Σ` is closed and totally disconnected, and `σ: L → Mod(Σ, E)` satisfies
`F∘σ = id_L`. If `x` had a finite orbit, then `L_x` would have finite index, and
restricting to classes fixing `x` gives `Mod(Σ, x)`. So the Birman sequence would
split over `L_x`, which Chen--Salter and the genus-3 claim exclude. Injectivity
of `σ` is not used.

**Consequence for hosts.** Suppose a host acts on a Cantor set of ends through
a Higman--Thompson group `V`, and contains `Mod(Σ)` through a forgetful section.
Then the image of `Mod(Σ)` in `V` has no finite orbit, so it is infinite.

### 3b. Type (A) self-actions

A type (A) action of a finite-index subgroup `G ≤ Mod(Σ)` would settle the target
through `type-a-action-gives-boone-higman-for-subgroups` and the finite-extension
closure. The pair clause kills every action whose stabilizers:
- are finite or normal;
- fix a multicurve (so curves, multicurves, and curve- or pants-graph vertices
  are out);
- are virtually cyclic.

**What is not decided.**
- Hull--Osin highly transitive actions, not re-read in this pass, satisfy the
  pair clause. So any obstruction must use finite generation of stabilizers.
- Actors that properly contain `Mod(Σ)`.

## 4. Host candidates

Sources were fetched on MSI: arXiv:1701.08132, 2110.05318, 2010.07225,
2001.04579, 2405.18354, 1007.1118, 2603.24687, 2506.02319, 2605.20564. Text
extraction on MSI failed, since `/usr/bin/python3.11` has neither `pypdf` nor
`pip`. The PDFs are being read page by page locally. Section 4 is filled in only
from pages actually read.

## 5. Status

`closed-surface-mapping-class-groups-satisfy-boone-higman` and
`boone-higman-conjecture` remain OPEN. Nothing here proves an embedding. The
two landed claims are obstructions to two specific construction shapes: forgetful
sections into Cantor-punctured hosts, and type (A) self-actions with small
stabilizers.
