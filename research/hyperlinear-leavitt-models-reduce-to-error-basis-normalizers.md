---
rg: 2
id: hyperlinear-leavitt-models-reduce-to-error-basis-normalizers
kind: claim
title: Approximate 24k models of the binary Leavitt unit group must approach the blockwise error-basis-normalizing class
distinct_from:
  leavitt-24k-models-avoid-blockwise-error-basis-normalizers: that is the proved exclusion, a positive lower bound on the distance to the class; this is the complementary recovery assertion, that approximate models cannot escape it, and the two together are contradictory unless no such models exist.
  leavitt-24k-feasibility-has-a-uniform-gap: that is the metric statement equivalent to nonhyperlinearity; this is a strictly stronger structural statement about the shape of approximate models, which implies it and is refuted outright if the group is hyperlinear.
  leavitt-24k-feasibility-vanishes: that is the hyperlinear branch; this is incompatible with it, so establishing this claim decides the branch negatively.
artifacts:
  - research/artifacts/leavitt-error-basis-normalizer-obstruction-2026-09-08.md
---

**OPEN.** In the notation of
`leavitt-24k-models-avoid-blockwise-error-basis-normalizers`, prove that
for every sequence of regular-factor `24k` tuples `X_n` with

```text
max_(r in T) ||r(X_n) - I||_(2,24 k_n) -> 0
```

one has `delta(X_n) -> 0`: the tuples approach the blockwise
error-basis-normalizing class in normalized Hilbert--Schmidt distance.

With the established exclusion this is contradictory, so proving it
proves that no such sequence exists, which gives
`leavitt-24k-feasibility-has-a-uniform-gap` and so nonhyperlinearity of
a nonsofic group.

## Attempts

- **Exactify each finite factor separately.** Both `C_3` and `C_2^3`
  already act by exact representations in the `24k` formulation, so
  there is nothing to round. Rounding them inside an ambient algebra
  produces two commuting-up-to-phase families but no **common** complete
  error basis and no common block decomposition respected by all four
  generators. This is exactly where the supplied argument stops, and no
  repair is known.
- **Read the direction of the implication before working it.** This is
  not a weaker stepping stone. If the group is hyperlinear then genuine
  model sequences with vanishing `T`-defect exist, and the established
  exclusion forces `liminf delta >= 1/(sqrt 2 B_0) > 0`, refuting this
  claim. So this claim implies nonhyperlinearity and is strictly stronger
  than the gap it would deliver. Anyone attacking it is attacking the
  whole question, not a fragment of it.
- **Why it is recorded anyway.** It names the single missing step of a
  proof whose other half is finished with explicit constants, and it
  fixes which enlargement of the model class would matter: the exclusion
  already covers arbitrary block counts, dimensions, phases, tensor
  padding and small perturbations, so a counterexample must be a tuple
  that is genuinely far from every error-basis normalizer, not a variant
  of the Clifford architecture.
- **Deferred alternative.** The other way to use the exclusion is to
  find a second uniform obstruction covering the tuples outside the
  class, rather than to prove that none exist. No candidate is recorded.
