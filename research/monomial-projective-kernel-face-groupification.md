---
rg: 2
id: monomial-projective-kernel-face-groupification
kind: route
title: Replace generator-visible Fourier clauses by a finite normal projective-kernel face
target: monomial-gap-phase-safe-toric-groupification
requires:
  - finite-phase-monomial-game-algebra-dictionary
  - toric-clause-spectra-cannot-generate-monomial-factor
  - projective-kernel-face-gap-compactifies-phase-safely
  - monomial-finite-phase-projective-kernel-face-separator
---

Take the finite two-player game and finite binomial determining list from
`monomial-finite-phase-projective-kernel-face-separator`.  The chosen extreme
monomial trace fixes every clause, so it supplies perfect commuting
completeness.  Equation `(MPK2)` excludes every weak-star limit of
finite-dimensional perfect states, hence gives `omega_qa<1` by the relative
finite-dimensional face criterion.

Compactness makes the list finite.  Its clauses lie in the normal graph
`C_chi`, so `(PKC4)` proves that their normal closure meets the scalar phase
group trivially.  This produces the output requested by
`monomial-gap-phase-safe-toric-groupification` without identifying the
Fourier projections with clause spectra—the identification ruled out by the
factorial centrality theorem.
