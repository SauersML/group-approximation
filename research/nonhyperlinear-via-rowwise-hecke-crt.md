---
rg: 2
id: nonhyperlinear-via-rowwise-hecke-crt
kind: route
title: Convert a rowwise Hecke-CRT certificate into a finite canonical HS obstruction
target: non-hyperlinear-group
requires:
  - oracularizable-tracial-nonru-game-exists
  - rowwise-hecke-crt-certificate-for-nonce-bcs
  - finite-row-mask-group-algebra-certificate-forces-nonhyperlinear
---

Choose the fixed finite perfect-commuting game with finite-dimensional gap.
The Hecke-CRT claim supplies its one global BCS tuple, independent row masks,
and strict weighted canonical deficit.  The finite row-mask theorem then
produces one finite multiplication-and-trace window with a positive
all-dimensions normalized-HS defect.  Hence the constructed ordinary group
is nonhyperlinear; no common carrier, convergence-rate estimate, recursive
diagonal, or finite-presentation hypothesis is needed.

