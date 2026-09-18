---
rg: 2
id: fpbs-bernoulli-cycle-tail-compactness-via-morse-deficit
kind: route
title: Vanishing Morse deficit gives Cayley subgraphings of cost near one plus beta_1, and the cycle identity converts that into tail compactness
target: fpbs-bernoulli-cycle-tail-compactness
requires:
  - fpbs-bernoulli-morse-collapse-criterion
  - fpbs-morse-deficit-vanishes-for-full-presentations
  - fpbs-graphing-cost-betti-cycle-dimension-identity
artifacts:
  - research/artifacts/fpbs/docs/bernoulli-morse-collapse-criterion.md
  - research/artifacts/fpbs/docs/cost-cycle-structure.md
---

Written derivation.

1. **Cheap subgraphings.** By `fpbs-morse-deficit-vanishes-for-full-presentations`, for every `eps > 0` there are an
   `L` and a Morse matching `M` for `P_L` with `mu(M) >= z(Phi_S) - eps`.
2. **Their cost.** By Theorem A of `fpbs-bernoulli-morse-collapse-criterion`, `Phi_S \ E_M` generates `R_b`, has
   bounded degree, and costs at most `1 + beta_1 + eps`.
3. **Near-minimizing sequence.** Taking `eps = 1/n` gives a bounded-degree near-minimizing sequence `Phi_n`, with
   `c(Phi_n) -> 1 + beta_1 = C(b)`. The lower bound `C(b) >= 1 + beta_1` comes from the identity.
4. **Tail compactness.** By the identity, `z(Phi_n) = c(Phi_n) - 1 - beta_1 -> 0`. Since `z_L(Phi_n) <= z(Phi_n)`,
   the tail `z(Phi_n) - z_L(Phi_n)` tends to `0` for every `L`. So the double limit in the target vanishes.

The route fires only if the open premise is proved. This is dependency bookkeeping, not a formal verification.
