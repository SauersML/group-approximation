---
rg: 2
id: private-origin-rows-permutation-proof
kind: route
title: The origin source enters one relay bijectively, and relays with forward-glued origin cells can be steered to any output
target: private-origin-rows-force-permutation-encoders
requires: []
artifacts:
  - research/artifacts/vh-lattice-table-hosts-2026-09-12.md
---

Section 7 of the artifact, Lemma F. It uses the network form of
`boolean-core-is-uniform-single-demand-network-coding`: one source per class, one relay
per row applying `mu`, one sink applying `nu`.

1. **The origin row is bijective in its origin cell.** The source `c_0` of the marked
   class feeds only relay `1_S`, at position `1_M`. With every other source fixed, the
   sink recovers `c_0` from `y_(1_S) = mu(c_0, rest)` and unchanged side relays. So
   `mu(., rest)` is a bijection of `A` for every `rest`.
2. **Steering.** Given any assignment and targets `t_1, ..., t_k`, change the origin
   source of `s_1, ..., s_k` in this order. By step 1 each change reaches its target.
   That source occurs elsewhere only in later rows, never in row `1_S`, so `c_0`,
   `y_(1_S)` and the relays already set keep their values.
3. **The origin relay decides alone.** Two assignments with equal `y_(1_S)` can be
   steered to equal side relays without changing their origin sources. The sink then
   returns equal symbols, so `y_(1_S)` determines `c_0`.
4. **Conclusion.** `mu(a, rest)` determines `a`, and each `mu(., rest)` is a bijection, so
   `mu(a, rest) = psi(a)` for one permutation `psi`.
