---
rg: 2
id: leavitt-resolvent-ring-is-fp-and-contains-q-proof
kind: route
title: The resolvent identity (N+1) s_1^(m-1) s_2 = m s_1^(m-1) s_2 and the tail-class model
target: leavitt-resolvent-ring-is-fp-and-contains-q
requires: []
artifacts:
  - research/artifacts/gq-referee-b-leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md
---

Direct proof, written in the target node:
- `1/m = t_2 t_1^(m-1) A s_1^(m-1) s_2`, from `N s_1^k = s_1^k (N+k)` and `N s_2 = 0`;
- non-vanishing from the action on `Q^(X)`, where `X` is the tail class of `2^∞`.

`gq-referee-b` checked it (report in `artifacts`).
