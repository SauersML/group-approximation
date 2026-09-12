---
rg: 2
id: fpbs-local-selector-route-proof
kind: route
title: Keep the selected a-edges and every failed root then close the torsion cycle
target: fpbs-local-selector-repair-geometry
requires: []
artifacts:
  - research/artifacts/fpbs/local-sparsifiers.md
  - research/artifacts/fpbs/scripts/replay_local_sparsifiers.py
  - research/artifacts/fpbs/local-sparsifier-checks.json
---

Section 4 proves the density identity and deterministic route under its supplied finite-detour hypotheses. The rule uses A union D, so every failure is repaired; no limiting connectivity or iid output assertion is used.

This route records a written proof or cited input; Cairn does not independently verify mathematics.
