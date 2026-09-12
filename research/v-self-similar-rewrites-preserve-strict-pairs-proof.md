---
rg: 2
id: v-self-similar-rewrites-preserve-strict-pairs-proof
kind: route
title: An injective homomorphism preserves every product coincidence, and a product pair is strict exactly when a factor is
target: v-self-similar-rewrites-preserve-strict-pairs
requires:
  - thompson-v-coset-stabilizers-contain-copies-of-v
  - strict-automata-live-on-canonical-table-groups
artifacts:
  - research/artifacts/thompson-v-linear-counterexample-targets-2026-09-12.md
---

Section 7 of the artifact.

1. `phi` is injective, so `phi(s) phi(m) = phi(s') phi(m')` exactly when `s m = s' m'`, and
   likewise for `m s`. The tables agree, and by `strict-automata-live-on-canonical-table-groups`
   the design and its tables decide strictness. Directly: `tau^phi` is `tau` transported to
   `V_U ~= V` (`thompson-v-coset-stabilizers-contain-copies-of-v`) and extended along the cosets
   of `V_U`. That extension preserves injectivity and surjectivity in both directions.
2. The product map is `tau_1 x tau_2` on `(A_1 x A_2)^V = A_1^V x A_2^V`, with left inverse
   `sigma_1 x sigma_2`. It is surjective exactly when both factors are.
