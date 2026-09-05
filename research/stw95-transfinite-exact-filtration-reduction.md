---
rg: 2
id: stw95-transfinite-exact-filtration-reduction
kind: claim
title: Exact tensoring reduces pure permanence through arbitrary continuous filtrations of separable algebras
artifacts:
  - research/artifacts/stw95-pure-tensor-permanence-wave-audit-2026-08-30.md
distinct_from:
  stw95-countable-exact-filtrations-reduce-pure-tensors: that allows a possibly nonseparable algebra but only a countable ordinal filtration; this assumes separability of the algebra and permits arbitrary ordinals, including uncountable-cofinality limits.
  stw95-exact-finite-ideal-filtration-reduction: that performs only finite induction; this permits a continuous filtration indexed by an arbitrary ordinal, handles countable-cofinality limits by Cu continuity, and shows that separability forces stabilization at every uncountable-cofinality limit.
---

Let `A` be separable and let `B` be exact.  Let
`(I_alpha)_(alpha<=gamma)` be a continuous increasing filtration of `A` by
closed ideals, indexed by an arbitrary ordinal, with

```text
I_0=0,                 I_gamma=A,
I_lambda=closure(union_(alpha<lambda) I_alpha)
```

at every limit ordinal.  If

```text
(I_(alpha+1)/I_alpha) tensor_min B
```

is pure for every successor stage, then `A tensor_min B` is pure.

Consequently, if separable exact algebras `A` and `B` have continuous
composition series indexed by arbitrary ordinals and the tensor product of
every pair of their simple successor quotients is pure, then
`A tensor_min B` is pure.
