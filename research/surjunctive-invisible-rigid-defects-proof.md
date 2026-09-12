---
rg: 2
id: surjunctive-invisible-rigid-defects-proof
kind: route
title: Push rigid pairs into metric ultraproducts, then read the root lamp of a surjunctive coset wreath
target: surjunctive-groups-carry-invisible-rigid-defects
requires:
  - sofic-groups-kill-rigid-compression-defects
  - kun-thom-nonsofic-wreaths-are-surjunctive
  - kt-lef-graph-wreaths-surjunctive-and-nonsofic
  - strict-pairs-transfer-to-table-realizations
artifacts:
  - research/artifacts/defect-window-automata-2026-09-12.md
---

Derivation (artifact Sections 2 and 3).

- **Invisibility.** Let `psi` be a homomorphism from `H` into a metric ultraproduct of
  symmetric groups. Its image is a countable subgroup of that ultraproduct, hence sofic.
  - `psi(Gamma)` and `psi(G)` are Kazhdan, as quotients of Kazhdan groups.
  - `psi(P_Gamma)` lies inside the compression semigroup of `psi(Gamma)` and generates
    `psi(G)`.
  - `psi(z)` centralizes `psi(Gamma)`.

  So the image is a sofic group containing a rigid pair, and
  `sofic-groups-kill-rigid-compression-defects` sends the defect to `1`.
- **Nontrivial in `W`.**
  - The root lamp `a_Gamma` centralizes `Gamma`, and `t a_Gamma t^-1 = a_(t Gamma)`.
  - Conjugating by `gamma` moves this lamp to `a_(gamma t Gamma)`.
  - The two sites differ because the stabilizer of `t Gamma` is `t Gamma t^-1`.
- **Surjunctive.** `kun-thom-nonsofic-wreaths-are-surjunctive`; for every graph,
  `kt-lef-graph-wreaths-surjunctive-and-nonsofic`.
- **Filter.** A realization of a strict pair's tables in `W` would, by
  `strict-pairs-transfer-to-table-realizations`, give a strict pair over the surjunctive
  group `W`.
