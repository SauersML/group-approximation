---
rg: 2
id: common-source-game-state-proof
kind: route
title: Pull all context measurements back to the common source
target: common-source-partial-isometries-decode-one-game-state
requires: []
---

On `Q C^d`, set `tilde P_(c,a)=S_c^*P_(c,a)S_c`.  Because the context atoms
reduce `S_cS_c^*`, these operators form a PVM and sum to `Q`.  Bob's binary
measurements restrict to `Q` because they commute with it.  Use the maximally
entangled state on `Q C^d` and its conjugate.

The forbidden probability is `||F_cS_c||_2^2/tau(Q)`.  Left multiplication
by `S_c^*` is Hilbert--Schmidt contractive, so the disagreement probability
is at most `||A_(c,x)S_c-S_cB_x||_2^2/(4tau(Q))`.  Averaging gives loss at
most `E_Q/tau(Q)`.  The game gap forces this to be at least `1-theta`.
