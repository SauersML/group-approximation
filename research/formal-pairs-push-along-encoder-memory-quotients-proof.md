---
rg: 2
id: formal-pairs-push-along-encoder-memory-quotients-proof
kind: route
title: Collapse the formal identity onto the encoder memory group, then substitute along the quotient map
target: formal-pairs-push-along-quotients-of-the-encoder-memory-group
requires: []
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
---

Artifact, Section 1, Theorem 1.
1. **Collapse onto `H`.** Choose left coset representatives, with `1` for `H`. The substitution
   `X_(ch,i) -> X_(h,i)` is a ring homomorphism fixing `X_(1,i)`. Since `M~ ⊂ H`, each encoder translate
   at a decoder cell `v = c_v h_v` becomes the `H`-translate at `h_v`. The image of the formal identity
   is a formal identity for `tau_H` with a decoder reading the cells `h_v`.
2. **Push along `rho`.** `X_(h,i) -> X_(rho(h),i)` is a ring homomorphism fixing `X_(1,i)`, and it
   carries `H`-translates of `tau~` to `Q`-translates of `tau~_rho`.
3. **Representation.** At points, `tau~_rho(y) = tau~(y o rho) = mu(y o rho)`, so `tau~_rho` represents
   `tau_rho`.
4. **Stable case.** Treat the ancilla tracks as extra tracks.
