---
rg: 2
id: known-type-artin-twisted-bt-groups-embed-in-fp-groups
kind: claim
title: For right-angled, spherical, euclidean, FC-type, large-type, 2-dimensional and rank-three Artin groups A, AV_A embeds in a finitely presented group
distinct_from:
  every-artin-twisted-brin-thompson-group-embeds-in-fp-group: that is the open affirmative answer to Zaremsky Problem 3.8 for every Artin group; this is the established answer for the Artin groups whose word problem is known to be solvable.
  artin-groups-satisfy-boone-higman: that asks for finitely presented SIMPLE envelopes of the Artin groups themselves; this gives finitely presented hosts, not necessarily simple, of the larger groups AV_A.
artifacts:
  - research/artifacts/zp-z3-08-twisted-bt-artin-2026-09-13.md
---

**ESTABLISHED** by `known-type-artin-twisted-bt-groups-embed-in-fp-groups-proof`.

Let `A` be an Artin group from one of the classes of
`known-artin-classes-have-solvable-word-problem`: right-angled, spherical, irreducible
euclidean, FC type, large type, dimension at most 2, rank three, or a finite direct
product of these. Then the twisted Brin–Thompson group `AV_A`, for the translation
action, embeds in a finitely presented group. The host can be chosen with solvable
word problem.

This is the partial yes answer to Zaremsky Problem 3.8. By
`self-twisted-bt-group-of-infinite-group-is-not-fp`, the host is always a proper
overgroup of `AV_A`.
