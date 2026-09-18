---
rg: 2
id: k2-central-in-steinberg-groups-via-k2-stability
kind: route
title: Centrality of K_2(N,R_L) is item 3 of the Leavitt resolvent K_2 stability theorem
target: k2-central-in-steinberg-groups-of-leavitt-resolvent-ring
requires:
  - leavitt-resolvent-k2-stability-holds
---

Item 3 of `leavitt-resolvent-k2-stability-holds` states that `K_2(N, R_L)` is central in
`St_N(R_L)` for every `N >= 3`. In particular this holds for every `N >= 5`, which is the
target.

Its item 2 identifies `K_2(N, R_L) ≅ Q^x` on the symbols `{λ, N+1}`. So the centre of
`St_N(R_L)` contains an infinitely generated central `Q^x`. This is the input of
`st-n-r-l-no-type-a-action-via-centre`, and of the centre clauses of
`fw-shell-inputs-at-window-zero-are-highly-transitive`.
