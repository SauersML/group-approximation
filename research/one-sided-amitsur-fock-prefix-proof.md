---
rg: 2
id: one-sided-amitsur-fock-prefix-proof
kind: route
title: Evaluate the alternating monomials on a prefix-free family of Fock isometries
target: one-sided-amitsur-oracle-has-bounded-fock-model
requires:
  - two-generator-amitsur-levitzki-dimension-oracle
---

For `j<k`, the words `w_j=xy^jx` and `w_k=xy^kx` first differ where
`w_j` has its terminal `x` and `w_k` still has `y`; neither is a prefix of
the other.  Unique parsing by this prefix code shows that two different
sequences of the same number of codewords give prefix-incomparable
concatenations.  Thus the Fock isometries in `(OAF4)` have orthogonal ranges.
Expanding the alternating sum proves `(OAF5)`, and `(OAF6)` supplies the
one-sided inverses simultaneously on full Fock space.

The matrix obstruction is the standard identity `(ALO3)` from
`two-generator-amitsur-levitzki-dimension-oracle`.  Substitution in the
`n=d` relation leaves `0-I`, whose normalized Hilbert--Schmidt norm is one.

