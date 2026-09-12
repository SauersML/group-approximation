---
rg: 2
id: formalizability-is-a-boolean-ideal-cokernel-class-proof
kind: route
title: Correct the decoder inside the Boolean ideal; the change is exactly the encoder lift applied to the correction
target: formalizability-is-a-boolean-ideal-cokernel-class
requires: []
artifacts:
  - research/artifacts/formalizability-obstruction-class-2026-09-12.md
---

Sections 1-2 of the artifact.

1. **Lifts preserve `I`.** For any lift `hat tau^*`,
   `hat tau^*(X_h^2 + X_h) = hat mu_h^2 + hat mu_h` maps to `y^2 + y = 0` in the
   Boolean ring `B`, so it lies in `I`. Hence `hat tau^*(I) subseteq I`.
2. **Exact correction.** With `hat tau^* hat sigma_0^*(X_h) = X_h + eps_h`,
   `eps_h in I`, replace `hat sigma_0^*(X_h)` by `hat sigma_0^*(X_h) + delta_h`,
   `delta_h in I`. This is again an algebra lift of `sigma^*`. Because `hat tau^*` is
   additive, `hat tau^* hat sigma^*(X_h) = X_h + eps_h + hat tau^*(delta_h)`. An
   algebra map is determined by generator values, so no higher-order terms appear.
   The formal identity holds iff `hat tau^*(delta_h) = eps_h` for all `h`.
3. **Cokernel class.** `hat tau^*(I) subseteq I` and `eps_h in I`, so solvability is
   vanishing of `[eps]` in `coker(hat tau^*|_I)`. Equivariance reduces the system to
   `n` equations, one per track.
4. **Decoder-side independence.** Another decoder lift shifts `eps_h` by
   `hat tau^*(delta'_h)`, `delta'_h in I`, i.e. within `hat tau^*(I)`, leaving `[eps]`
   unchanged.
5. **Sitewise vanishing.** For memory `{1}`, `tau` is a permutation of `F_2^n`, a
   composite of edge shears, each a formal involution; so `hat tau^*` is an
   automorphism of `R`, `hat tau^*|_I` is bijective, and `[eps] = 0`.

The route establishes the stated equivalence and the two special facts; it does not
decide whether `[eps]` vanishes in general.
