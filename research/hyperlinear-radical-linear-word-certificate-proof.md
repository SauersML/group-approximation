---
rg: 2
id: hyperlinear-radical-linear-word-certificate-proof
kind: route
title: Choose tolerance one in radical compactness and linearize its fixed gap
target: hyperlinear-radical-has-linear-word-certificate
requires:
  - hyperlinear-radical-presentation-compactness
  - fixed-hs-word-gap-is-linear-domination
artifacts:
  - research/artifacts/hyperlinear-word-certificate-2026-09-07.md
---

Compactness at word tolerance one supplies a finite relator list R_0
and eta>0 with delta_(R_0)<eta implying ||w-I||_2<1. Contrapose and use
the fixed-gap linearization. Squaring gives

```text
||w(U)-I||_2^2 <= (4/eta^2) max_(r in R_0)||r(U)-I||_2^2
              <= N sum_(r in R_0)||r(U)-I||_2^2
```

for any positive integer N>=4/eta^2. Conversely the finite sum vanishes
along every tuple defining a matrix-ultraproduct homomorphism from Gamma,
so the word also vanishes. Enlarging R_0 to all relators in a finite
presentation preserves the inequality.

If w is nontrivial in Gamma, it stays nontrivial in <S|R_0> because
that group surjects onto Gamma. The inequality forbids a faithful
hyperlinear embedding. For an infinite simple group, every nontrivial
ultraproduct homomorphism would be faithful, so nonhyperlinearity is
equivalent to the radical condition for any chosen nontrivial word.

The artifact also evaluates the proposed energy polynomial at the left
regular tuple: its trace is -2. This excludes universal tracial SOS
proofs of a nontrivial instance and leaves a matrix-specific proof as
the unresolved input.
