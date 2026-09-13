---
rg: 2
id: central-bernoulli-lifts-force-splitting
kind: claim
title: Over a w-rigid base, a Bernoulli shift lifts across a finite central kernel only if the central extension splits
distinct_from:
  bernoulli-lifts-across-finite-kernels-force-virtual-splitting: that gives virtual splitting for every finite normal kernel through an invariant measure on the quotient; this gives actual splitting for central kernels through the flip across independent copies.
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-degree-one-reduction-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by `central-bernoulli-lifts-force-splitting-proof`.

Let `Gamma` be w-rigid (for instance infinite with property (T)), `A` finite abelian, and
`1 -> A -> Gamma~ -> Gamma -> 1` central with class `alpha`. If `[0,1]^Gamma` is the `A`-quotient of a free p.m.p.
`Gamma~`-action, then `alpha = 0`.

**Mechanism.** Write the lift as `delta b = alpha_0`.
- The difference `d = b(x) - b(x')` over two independent copies is an honest 1-cocycle into `A`.
- Popa makes `d` cohomologous to a homomorphism. Ergodicity on three copies kills the homomorphism and separates the
  variables, so `b` is a coboundary plus a constant cochain `a`, and `alpha_0 = delta a`.

**Model test.**
- **Hypothesis side.** For `alpha = 0`, `Bern x A` lifts. For a virtually split `alpha != 0`, the liftable actions
  induced from a split finite-index subgroup have finite factors and are not Bernoulli, consistent with the claim.
- **Conclusion side.** Deligne's triple cover is not split, and the claim excludes Bernoulli lifts there, agreeing
  with `bernoulli-lifts-across-finite-kernels-force-virtual-splitting`.
