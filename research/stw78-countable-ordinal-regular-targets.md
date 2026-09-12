---
rg: 2
id: stw78-countable-ordinal-regular-targets
kind: claim
title: Arbitrary ordinal regular composition series solve LXXVIII
artifacts:
  - research/artifacts/stw78-finite-quasitrace-seed-audit-2026-08-30.md
---

Let `B` be a nonzero unital separable nuclear C-star algebra with no
normalized 2-quasitrace.  Suppose there are an arbitrary ordinal `lambda`
and a continuous increasing family of closed ideals

```text
0=I_0 <= I_1 <= ... <= I_lambda=B                       (1)
```

such that

```text
I_gamma = closure(union_(beta<gamma) I_beta)
```

at every limit ordinal `gamma<=lambda`, and every nonzero successor layer

```text
D_beta=I_(beta+1)/I_beta       (beta<lambda)
```

is algebraically simple and has almost-unperforated `W(D_beta)`.

Then `B` is `O_infinity`-stable and strongly purely infinite.  Every nuclear
homomorphism from a separable exact C-star algebra into `B` is strongly
`O_infinity`-stable.  In particular every LXXVIII map into `B` is
`O_infinity`-stable.

At a limit of countable cofinality, continuity gives a sequential inductive
limit along a cofinal sequence.  At a limit of uncountable cofinality,
separability forces the ideal chain to have stabilized below that limit.
Thus no uncountable inductive-limit permanence theorem is assumed.
