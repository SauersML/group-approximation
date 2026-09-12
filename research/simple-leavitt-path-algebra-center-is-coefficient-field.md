---
rg: 2
id: simple-leavitt-path-algebra-center-is-coefficient-field
kind: claim
title: The centre of a simple unital Leavitt path algebra of a finite graph is its coefficient field
distinct_from:
  leavitt-center-is-coefficient-field: that is proved internally for the binary Leavitt algebra L_k(1,2) by a kill-word sandwich; this is the statement for every simple Leavitt path algebra of a finite graph, where supports end at several vertices.
artifacts:
  - research/artifacts/bh-leavitt-path-steinberg-hosts-2026-09-12.md
---

**OPEN (citation to import, or internal proof).** Let `E` be a finite graph with
`L_K(E)` simple. Then `Z(L_K(E)) = K · 1`. In particular, over `F_2` every
central unit equals `1`, which is the `hcentral` hypothesis of the Lean
root-detection theorem (`GroupApproximation/Leavitt/RootDetectionBinary.lean`).

## Attempts

- **Expected source, not yet read:** Aranda Pino--Crow, *The center of a Leavitt
  path algebra* (Rev. Mat. Iberoam. 2011).
- **Internal route (sketch only).** Adapt `leavitt-center-kill-word-sandwich-proof`.
  - For central `z`, sandwich by the paths of steps 1--3 of
    `leavitt-path-simultaneous-division-proof`. Centrality gives
    `η* z x = z η* x`.
  - The sandwich of every bounded monomial is `0` or a vertex idempotent at `c_0`.
  - The step from "scalar at `c_0`" to "scalar at `1`" is not written; it needs
    the transport `S* c_0 S = 1` together with centrality.
