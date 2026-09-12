---
rg: 2
id: perfect-groups-have-no-triangular-models-with-trivial-diagonal
kind: claim
title: A perfect group acting upper triangularly with trivial diagonal blocks acts trivially
artifacts:
  - research/artifacts/el3-rank-model-extensions-2026-09-12.md
---

Let `Gamma` be a perfect group, `M` a unital ring, and `1 = h_1 + ... + h_m` pairwise
orthogonal idempotents. Let `sigma : Gamma -> M^x` be a homomorphism with
`h_s sigma(g) h_r = 0` whenever `s > r`, that is, a model preserving the finite flag
`(h_1 + ... + h_t) M` split by the `h_t`.

1. Each diagonal compression `sigma_t(g) = h_t sigma(g) h_t` is a homomorphism
   `Gamma -> (h_t M h_t)^x`.
2. If every `sigma_t` is trivial, then `sigma` is trivial.

Consequence: for a perfect group, trivial homomorphisms into `M^x` are closed under finite
extensions split by idempotents. Non-split extension terms carry no room once the graded
pieces are trivial.

**ESTABLISHED** by `perfect-group-triangular-model-proof` (artifact Section 1).
