---
rg: 2
id: failed-hs-word-bounds-have-rational-witnesses
kind: claim
title: Every failed ordinary HS word coefficient has an exact rational unitary witness
distinct_from:
  hyperlinear-radical-has-linear-word-certificate: that characterizes existence of some valid finite coefficient; this semidecides failure of one proposed rational coefficient and supplies no successful one.
  hyperlinear-computable-hs-dehn-modulus-solvable-word-problem: that races two searches using an assumed trivial-word modulus; this requires no modulus and tests one specified global word-energy inequality.
artifacts:
  - research/artifacts/hs-word-certificate-rational-search.md
  - experiments/hs_word_certificate.py
  - experiments/test_hs_word_certificate.py
---

For a finite word list R, a word w, and a positive rational C, failure of

```
e_w(U) <= C sum_(r in R) e_r(U)
```

in any finite matrix dimension is equivalent to a strict violation on
exactly unitary matrices over Q(i), and also to a strict violation on
rational skew-Hermitian Cayley transforms. Here e is squared normalized
Hilbert--Schmidt distance from the identity, including scalar phases.

Failure is uniformly semidecidable by a fair exact rational enumeration.
Validity of a specified coefficient is a Pi-zero-one predicate; no
hardness or decidability claim follows. Finite searches without a witness
are inconclusive, and no nontrivial radical word is supplied.
