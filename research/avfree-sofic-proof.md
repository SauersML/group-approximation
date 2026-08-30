---
rg: 2
id: avfree-sofic-proof
kind: route
title: Split over a finite-index free subgroup and amalgamate amenably
target: abelian-by-virtually-free-groups-are-sofic
requires: []
---

Choose a normal finite-index free subgroup `F normal Lambda` and let

```text
Gamma_0=A semidirect F normal A semidirect Lambda.
```

Write `F=F_r` with free basis `s_1,...,s_r`. Then

```text
A semidirect F_r
 = (A semidirect_(s_1) Z) *_A ... *_A (A semidirect_(s_r) Z).  (AVF1)
```

Each `A semidirect Z` is amenable because both its normal subgroup `A`
and quotient `Z` are amenable. Amalgamated free products of sofic groups
over an amenable subgroup are sofic, so `(AVF1)` makes `Gamma_0` sofic.
Finally

```text
(A semidirect Lambda)/Gamma_0 isomorphic_to Lambda/F
```

is finite and hence amenable. The standard valid extension theorem — a
group with sofic normal subgroup and amenable quotient is sofic — proves
`A semidirect Lambda` sofic.

No finite-generation assumption on `A` is used. The passage through `F`
is load-bearing: soficity of an arbitrary extension with amenable kernel and
sofic quotient is not known, even for finite kernels, so it cannot replace
`(AVF1)`.
