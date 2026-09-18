---
rg: 2
id: leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1-proof
kind: route
title: The swap matrix W is elementary, so the Leavitt swindle runs in rank 3N+1 with centralizing coefficients
target: leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1
requires:
  - leavitt-pairs-embed-sl-n-q-in-steinberg-groups
artifacts:
  - research/artifacts/gq-referee-a-leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1.md
  - research/artifacts/gq-referee-b-leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1.md
---

Take steps (a)–(f) of `leavitt-pairs-embed-sl-n-q-in-steinberg-groups`, which are established, and change two
things (Attempt 1 of the target):
1. `W` factors into elementary matrices: `U_2 U_1 W U_3 = [[0, -I_2N], [I_N, 0]] ∈ E_3N(Z)`. So `D = W` and the
   rank is `3N+1`.
2. The coefficients may be any subring `A` commuting with the Leavitt pair. That commutation is the only property
   step (b) uses.

Part 2 then applies part 1 to `(M_k(S), M_k(Q))`, with `M_k(S) ≅ S` built from the pair, and uses
`E_3(M_k(Q)) = SL_3k(Q)`. `gq-referee-a` and `gq-referee-b` both PASS it.
