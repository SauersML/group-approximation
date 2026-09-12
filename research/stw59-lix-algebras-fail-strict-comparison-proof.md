---
rg: 2
id: stw59-lix-algebras-fail-strict-comparison-proof
kind: route
title: The LIX algebras are simple unital AH and not K1-injective
target: stw59-lix-algebras-fail-strict-comparison
requires: [simple-ah-strict-comparison-is-k1-injective, stw59-simple-ah-non-k1-injective, stw59-exact-finite-abelian-unitary-component-groups]
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

The stages `Gamma(X_i, End E_i)` sit over finite CW complexes. Embedding
`E_i` in a trivial bundle with range projection `p` identifies each stage
with the corner `p M_n(C(X_i)) p`, so every LIX algebra is a unital simple AH
algebra.

The second and third prerequisites supply unitaries that are not
null-homotopic but have vanishing K1 class. So none of these algebras is
K1-injective. By the first prerequisite none has strict comparison. Square.
