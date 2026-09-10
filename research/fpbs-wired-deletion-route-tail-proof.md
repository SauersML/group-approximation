---
rg: 2
id: fpbs-wired-deletion-route-tail-proof
kind: route
title: Thin the wired forest to finite components and charge short ambient routes to deleted edges
target: fpbs-quantitative-routing-tail-bound
requires:
  - fpbs-wired-forest-degree-two
artifacts:
  - research/artifacts/fpbs/routing-obstruction-continuation.md
  - research/artifacts/fpbs/scripts/replay_routing_bound.py
  - research/artifacts/fpbs/routing-bound-replay.json
---

Sections 2-3 of the artifact give the mathematical proof. Independent eta-thinning of F has finite components and deletes intensity delta+eta from H. Their ambient boundary has expected root incidence at least h by mass transport. A generator pair separated by this finite partition either has H-distance greater than R or sees a deleted edge internal to B_R. The latter probability is at most |B_R|(delta+eta). Let eta decrease to zero. The replay checks only finite witness/incidence inequalities, not the infinite prerequisites.
