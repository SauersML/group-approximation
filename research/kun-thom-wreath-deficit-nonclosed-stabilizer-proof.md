---
rg: 2
id: kun-thom-wreath-deficit-nonclosed-stabilizer-proof
kind: route
title: Place the witness subgroup in a finite-orbit wreath and separate lamps by fibre sums over closed stabilizers
target: kun-thom-wreath-deficit-witnesses-need-nonclosed-stabilizers
requires: [sofic-radical-localizes-bernoulli-deficit-witnesses]
artifacts:
  - research/artifacts/kun-thom-wreath-rokhlin-test-case-2026-09-12.md
---

Section 4 of the artifact.

1. **Where K sits.** `(n, g)(n', g') = (n + g.n', gg')` and `(n, g)^-1 = (-g^-1.n, g^-1)`, so the lamp
   parts of `K` are supported in the finite union `O` of `π(K)`-orbits of the generator lamp sites. So
   `K <= V = B^(O) ⋊ π(K)`.
2. **Amenable image.** If `π(K)` is amenable, `K` is locally-finite-by-amenable, hence amenable and
   sofic.
3. **Closed stabilizers.** Suppose every stabilizer `S_i` is closed in `π(K)`, which is residually
   finite. For `(n, 1) != 1` with finite support `T`, pick a finite-index normal `Δ` separating the
   points of `T` modulo `S_i Δ`. On `Ō = ⊔_i π(K)/(S_i Δ)` the group `Δ` acts trivially. Fibre sums give
   a homomorphism `V -> B^Ō ⋊ π(K)/Δ` into a finite group that does not kill `n`. Actor parts are
   detected by finite quotients of `π(K)`. So `V`, and hence `K`, is residually finite, and therefore
   sofic.
4. **Conclusion.** A sofic `K` has trivial sofic radical, and the prerequisite excludes every
   configuration with `Φ < log q` over it. So a witness must violate 2 or 3.
