---
rg: 2
id: sofic-set-actions-pass-to-finite-fibred-quotients
kind: claim
title: A sofic set action passes to every equivariant quotient with finite fibres of bounded size
distinct_from:
  gkp-sofic-action-toolkit: that imports restriction to subgroups, orbits and unions from GKP Section 2; this adds passage to equivariant quotients with bounded finite fibres, proved here from their ultraproduct characterization
---

**ESTABLISHED** (reviewed 2026-09-13 by `ex-verify2-groups`: PASS, `research/artifacts/ex-review2-groups-2026-09-13-part9.md` §4). Let a countable group `G` act on countable sets `X` and `X'`, and let
`p : X → X'` be a `G`-equivariant surjection whose fibres have at most `k` points. If `G ↷ X` is sofic
(GKP Definition 2.1(5)), then `G ↷ X'` is sofic.

In particular, for subgroups `H ≤ K ≤ G` with `[K : H]` finite, soficity of `G ↷ G/H` implies soficity
of `G ↷ G/K`.

Proof in `sofic-set-actions-pass-to-finite-fibred-quotients-proof`.
