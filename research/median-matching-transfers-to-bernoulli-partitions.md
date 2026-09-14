---
rg: 2
id: median-matching-transfers-to-bernoulli-partitions
kind: claim
title: The median device has Kazhdan components to match in the Bernoulli setting over the Leavitt units
refuted_by:
  - median-matching-has-no-bernoulli-entropy-analogue
distinct_from:
  openai-bounded-median-component-matching: that is the established device on almost-actions of finite sets; this asks for the objects it acts on inside the uniform Bernoulli shift over the Leavitt units or inside the group itself.
artifacts:
  - research/artifacts/median-matching-entropy-translation-2026-09-12.md
---

**REFUTED.** Let `Gamma = EL_alpha(R) ≅ EL_3(R)` be the Kazhdan subgroup of
`openai-nine-leaf-leavitt-configuration`, with a finite symmetric generating set `S`, inside
`U = L_(F_2)(1,2)^x`. The claim is that at least one of the following holds:

1. some bounded measurable `Gamma`-invariant function on the uniform Bernoulli shift `(A^k)^U` is not
   a.e. constant;
2. some finite nonempty subset of `U` is preserved by every `s in S`.

This is what a certificate built by `openai-bounded-median-component-matching` needs:
* either nontrivial `Gamma`-components on the shift, whose sizes the median normalization compares;
* or a finite set that the generators permute, where the no-drift identity is exact.

Both fail. `Gamma` is infinite and Kazhdan, hence nonamenable. So (1) contradicts Theorem 1 and (2)
contradicts Proposition 2(1) of the artifact. This is recorded as a claim, so that
`leavitt-zero-supremum-via-median-matching` names its missing step instead of carrying it as a prose
caveat.

## Attempts

- *Refuted 2026-09-12* by `median-matching-has-no-bernoulli-entropy-analogue`.
- *Non-free variants* are outside this claim. On a generalized Bernoulli shift over `U/H` in which
  `Gamma` has a finite orbit, (1) holds. That action is not free, and a Rokhlin entropy deficit of it
  does not bear on `leavitt-units-have-zero-rokhlin-entropy-supremum`.
