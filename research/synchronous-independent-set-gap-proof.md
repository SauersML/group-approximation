---
rg: 2
id: synchronous-independent-set-gap-proof
kind: route
title: Use the synchronous reverse decoder before the almost-synchronous loss
target: synchronous-independent-set-reduction-preserves-a-quadratic-gap
requires: []
artifacts:
  - research/artifacts/independent-set-rounding-rank-router-2026-08-23.md
---

Mančinska--Spaas--Spirig--Vernooij Lemma 5.1 proves that target
independent-set loss `delta` produces source loss `O(sqrt(t delta))` for a
synchronous strategy.  Contraposition gives `(SIG1)`.  In the target game,
same-vertex answers on distinct questions and graph-adjacent answers are
exactly the losing pairs.  For projections, traciality gives
`tau(PQ)=||PQ||_2^2`, proving `(SIG2)`.  No almost-synchronous rounding is
invoked, so the later eighth-power theorem is intentionally bypassed.

