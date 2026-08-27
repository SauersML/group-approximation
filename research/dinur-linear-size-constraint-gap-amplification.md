---
rg: 2
id: dinur-linear-size-constraint-gap-amplification
kind: claim
title: Dinur amplification doubles constraint unsat with linear blowup and bounded alphabet after composition
---

For every fixed finite alphabet there are constants `C<infinity` and
`alpha>0`, a fixed output alphabet, and a polynomial-time transformation of
finite binary constraint graphs

```text
G |-> Amp(G)
```

such that

```text
size(Amp(G)) <= C size(G),
UNSAT(G)=0  implies  UNSAT(Amp(G))=0,
UNSAT(Amp(G)) >= min(2 UNSAT(G),alpha).                         (DGA1)
```

The transformation is preprocessing to a constant-degree expander with
self-loops, constant-length graph powering, and assignment-tester
composition. Iteration turns an inverse-polynomial gap into a constant gap
with polynomial total size. The powering lemma is the anti-localization
component: a bad edge hit in the middle of a random walk makes a positive
fraction of powered constraints fail, while expansion controls repeated
hits.

This is Irit Dinur, *The PCP theorem by gap amplification* (JACM 54(3),
2007), Theorem 1.5 together with Lemmas 1.6--1.8. It is a classical
constraint-mass theorem. It does not by itself convert `UNSAT` into
normalized-HS energy or preserve shared noncommutative packet carriers.

