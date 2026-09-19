---
rg: 2
id: toeplitz-transitive-actor-rounds-relative-clifford-cell
kind: route
title: Exactify the finite Pauli-linear head and apply the four-orbit Reynolds estimate
target: toeplitz-transitive-pauli-actor-repairs-relative-cell
requires:
  - bounded-involutive-cayley-expanders-for-sl-n-two
  - toeplitz-finite-head-centralizes-deep-tail
  - finite-schur-clifford-packet-flexible-hs-exactification
---

At level `n`, flexibly exactify the polynomially presented finite group
`P_n semidirect SL_n(2)` as in `(TPA5)`.  The upper-unitriangular faithful
model and Toeplitz Gaussian elimination make the multiplication-table
derivation loss polynomial rather than exponential in `|P_n|`.  Restriction
of the corrected table to `SL_n(2)` is an exact actor representation.

Average the proposed new-cell matrix over that actor.  The Cayley gap bounds
its distance to the actor fixed space.  On the average, commutator norms are
constant on the four orbits `(TPA3)`; insert the four prototype bounds into
the exact Weyl Reynolds square function.  This is `(TPA7)`.

Unlike `toeplitz-expander-rounds-relative-clifford-cell`, this route never
identifies a Clifford normalizer with `C_s tensor I`.  It uses an honest
linear actor subgroup after flexible exactification, plus four mixed Pauli
prototypes, so the external actor representation cancels under conjugation.
