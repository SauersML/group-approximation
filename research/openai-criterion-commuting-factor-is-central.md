---
rg: 2
id: openai-criterion-commuting-factor-is-central
kind: claim
title: In a sofic compressed Kazhdan pair the conjugated commuting factor is central in the compressed group
distinct_from:
  openai-expander-matching-criterion: that is Proposition 2.3 of the OpenAI chapter, concluding that the commuting factor is LEF; this derives from the rigid defect criterion the strictly stronger conclusion that its conjugate lies in the center of Gamma, so it is abelian, without using Gamma cap J = 1 or finite generation of J.
  one-sided-compression-nonsofic-criterion: that is the kernel-checked bridge from a non-LEF commuting factor to nonsoficity through a selected expander; this is an abelian-factor conclusion obtained from Kun--Thom normalization, not through expander selection.
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

**ESTABLISHED.** Let `Gamma <= G` be groups with property (T), with

```text
G = <Gamma, t_1, ..., t_m>,     t_i Gamma t_i^-1 <= Gamma,
```

and let `J <= G` satisfy `[Gamma, J] = 1` and `t_1 J t_1^-1 <= Gamma`. If `G`
is sofic, then

```text
t_1 J t_1^-1 <= Z(Gamma),                                         (ABEL)
```

so `J` is abelian.

*Proof.* `Gamma` is infranormal in `G` and `J <= C_G(Gamma)`. Apply
`sofic-groups-kill-rigid-compression-defects` with `H = G`, `g = t_1` and
`z = j`. Then `t_1 j t_1^-1` commutes with every element of `Gamma`, so
`t_1 J t_1^-1 <= Gamma cap C_G(Gamma) = Z(Gamma)`. ∎

## What this adds to the OpenAI criterion

Finitely generated abelian groups are residually finite, hence LEF. So
(ABEL) contains the original Proposition 2.3 ((T) of both groups), whose
conclusion is that `J` is LEF. The hypotheses `Gamma cap J = {1}` and finite
generation of `J` are not used. In the Leavitt application `J` is Thompson's
`V`, which is nonabelian, so (ABEL) fails outright.

The proof goes through Kun--Thom's normalization theorem rather than the
single-expander selection. The OpenAI selection argument and Kun--Thom's
cluster-groupoid medians are two finite-stage routes to the same group-level
fact.

Derivation: `openai-commuting-factor-central-proof`.
