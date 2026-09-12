---
rg: 2
id: thompson-v-is-f2-linear-sofic
kind: claim
title: Thompson's V is F_2-linear sofic
refuted_by:
  - thompson-v-has-no-nontrivial-f2-rank-model
distinct_from:
  thompson-v-is-sofic: that is soficity, approximation by permutations in Hamming distance; this is approximation by matrices over F_2 in normalized rank, which soficity implies and which is not known to imply soficity.
  binary-leavitt-unit-group-is-f2-linear-sofic: that is F_2-linear soficity of the binary Leavitt units, which contain V; linear soficity passes to subgroups, so that claim implies this one, but not conversely.
artifacts:
  - research/artifacts/thompson-v-rank-models-cantor-covariance-2026-09-12.md
---

**OPEN.** There is an injective homomorphism

```text
V -> prod_(k->omega) GL_(n_k)(F_2) / d_omega,     d(a,b) = rank(a - b) / n_k.
```

Equivalently, `V` has a nontrivial homomorphism into a characteristic-two matrix rank ultraproduct.
`V` is simple, so a nontrivial homomorphism is injective. Upgrading an injective homomorphism to
approximations with a uniform separation constant uses the Arzhantseva–Paunescu amplification. No
node here depends on that step.

**Consequences.**
- It refutes `thompson-v-has-no-nontrivial-f2-rank-model`.
- By `thompson-v-linear-witness-supports-kill-g-in-rank-models`, it kills the binary V target
  `thompson-v-order-three-averaging-idempotent-is-full` at the support level.
- It follows from `thompson-v-is-sofic` through `thompson-v-f2-linear-sofic-from-soficity`.

## Attempts

- **Covariant truncations of the Cantor action.** Dead:
  `thompson-v-cantor-system-has-no-covariant-rank-model` invalidates
  `thompson-v-f2-linear-sofic-via-covariant-cantor-truncation`.
- **Permutation-type models.** Monomial models are Hamming models
  (`monomial-rank-models-are-hamming-models`), so building one is exactly as hard as proving `V` sofic.
- **Leavitt-algebra models.** A rank model of `L_(F_2)(1,2)` restricted to the prefix-replacement units
  would give one of `V`. None exists (`leavitt-algebra-has-no-unital-rank-model`), so any model has to
  be non-multiplicative on the algebra.
- **What survives.** Genuinely non-monomial models that are not covariant for the cylinder idempotents,
  and do not factor through the Leavitt algebra. No candidate is known.
