---
rg: 2
id: fpbs-local-sparsifier-replay-evidence
kind: route
title: Run the exact finite local sparsifier script and retain its scoped output
target: fpbs-local-sparsifier-finite-replay
requires: []
artifacts:
  - research/artifacts/fpbs/local-sparsifiers.md
  - research/artifacts/fpbs/scripts/replay_local_sparsifiers.py
  - research/artifacts/fpbs/local-sparsifier-checks.json
---

The script uses Python standard-library integers, fractions, explicit finite group multiplication, and breadth-first searches. Its explicit unverified scope is retained in the JSON.

This route records a written proof or cited input; Cairn does not independently verify mathematics.
