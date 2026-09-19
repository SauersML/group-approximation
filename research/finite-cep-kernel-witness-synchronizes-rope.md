---
rg: 2
id: finite-cep-kernel-witness-synchronizes-rope
kind: claim
title: A finite-CEP embedding makes the graph benign witness rope profinitely synchronized
artifacts:
  - research/artifacts/three-bridge-finite-cep-rope-route-2026-08-25.md
distinct_from:
  quotient-benign-rope-synchronizes-finite-quotients: that assumes one map from the benign overgroup to the whole quotient and therefore forces finite presentability; this uses a different finite map for each finite quotient and has no retract consequence.
  profinite-synchronized-hnn-is-regular-mf: that consumes synchronized quotients analytically; this constructs them algebraically for the graph benign witness.
---

Let `F` be a finite-rank free group, `N` normal in `F`, `Q=F/N`, and suppose
`j:Q->P` embeds `Q` in a finitely presented effectively residually finite
group.  Assume the embedding has effective finite CEP in the refining form

```text
for every finite beta:Q->B, some finite r:P->C satisfies
ker(r j) <= ker(beta).                                       (FCK1)
```

Use the graph benign witness

```text
K=F times P,        e(f)=(f,1),
L={(f,j(q(f))):f in F}.                                     (FCK2)
```

Then `L intersect e(F)=e(N)`, the first rope group

```text
Gamma=<K,v | [v,L]=1>
```

is effectively residually finite, and the final rope edge has an effective
cofinal family of finite quotients satisfying `(RPS1)`.

Unlike a homomorphism `K->Q` killing `L`, `(FCK1)` is quotient-by-quotient
and only refines each requested finite congruence.  It therefore does not
make `Q` a retract of a finitely presented group.
