---
rg: 2
id: hyperlinear-implies-sofic-via-markovization
kind: route
title: Markovize each regular unitary window and use automatic Birkhoff integrality
target: hyperlinear-implies-sofic
requires:
  - regular-character-markovization
  - markov-sofic-equals-sofic
---

Let `G` be hyperlinear, fix a finite window containing identities, products and
inverses, and fix `eps>0`. Apply `regular-character-markovization` at a
sufficiently small output tolerance. Hyperlinearity supplies the required
unitary microstate, and the claim returns one common-state-space doubly
stochastic approximate table with regular trace separation. By
`markov-sofic-equals-sofic`, that table rounds to permutations with Hamming
multiplication defect and fixed-point error tending to zero. Since the window
and tolerance were arbitrary, `G` is sofic.
