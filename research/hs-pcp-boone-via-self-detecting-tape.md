---
rg: 2
id: hs-pcp-boone-via-self-detecting-tape
kind: route
title: Combine the Boone word, coRE verifier, multiplicity oracle and constant-HS groupification
target: hs-pcp-boone-compiler
requires:
  - boone-commutator-criterion-for-halting
  - kleene-mipco-self-destroying-game
  - finite-predicate-signed-permutation-sector
  - two-generator-amitsur-levitzki-dimension-oracle
  - multiplicity-pi-turing-tape
  - conjugacy-compressed-dimension-trigger
  - constant-hs-sound-self-detecting-tape-groupification
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
---

Use the Boone commutator as the exact marked word whose nontriviality records
nonhalting.  Compile the constant-gap local verification supplied at game
level by the coRE fixed point into the finite CPU of
`constant-hs-sound-self-detecting-tape-groupification`.  On its selected
`pi`-sector, the commutant is the multiplicity tape and the two-generator
Amitsur--Levitzki sequence forces a zero at the finite multiplicity index.

The groupification claim makes that trigger a robust finite control event and
propagates it to the marked Boone word with a universal normalized-HS
constant.  `conjugacy-compressed-dimension-trigger` prevents the final flag
itself from reintroducing runtime loss.  These give `(HPB2)`, while the exact
Boone criterion and the nonhalting branch give `(HPB1)`.  Hence the complete
HS--PCP Boone compiler follows.
