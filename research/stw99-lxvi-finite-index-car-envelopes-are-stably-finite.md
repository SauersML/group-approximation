---
rg: 2
id: stw99-lxvi-finite-index-car-envelopes-are-stably-finite
kind: claim
title: Finite-index expected envelopes of stably finite cores are stably finite
distinct_from:
  stw99-lxvi-car-stabilization-destroys-finite-seed: that rules out tensoring a non-stably-finite seed by CAR; this rules out finite-index ambient extensions of CAR, without assuming a tensor-product form.
  stw99-lxvi-central-matrix-sequence-obstruction: that forbids asymptotically central matrix tails when the double is infinite; this forbids every finite Watatani-index expected CAR inclusion, with no centrality hypothesis.
  stw99-lxvi-k0-dyadic-divisibility-obstruction: that tests the unit class in K0; this applies even when the full coherent CAR chain is already present and uses finite module index instead.
artifacts:
  - research/artifacts/stw99-lxvi-coherent-car-no-go-audit-2026-08-30.md
---

Let `D subset A` be a unital inclusion of unital C*-algebras.  Suppose that
`D` is stably finite and there is a conditional expectation

```text
E:A->D
```

of finite Watatani index; equivalently, `E` admits a finite quasi-basis.
Then `A` is stably finite.

Consequently, no solution of STW Problem LXVI can admit a finite-index
conditional expectation from the ambient algebra onto the embedded CAR
algebra.  The same obstruction applies to either equivalent finite
CAR-containing seed: its CAR inclusion must have infinite module index.

In particular, none of the following can construct an LXVI witness:

1. a finite-group crossed product of the CAR algebra, with its canonical
   coefficient expectation;
2. a finite tower of finite-index expected extensions starting from CAR; or
3. an injective inductive limit of such stably finite finite-index stages.

No simplicity, exactness, nuclearity, trace, quasitrace, `K_0` condition, or
centrality of the included core is assumed.
