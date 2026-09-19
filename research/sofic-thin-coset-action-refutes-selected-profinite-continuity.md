---
rg: 2
id: sofic-thin-coset-action-refutes-selected-profinite-continuity
kind: claim
title: Soficity of the thin SL3 coset action refutes selected profinite continuity
distinct_from:
  sofic-coset-action-refutes-sl3-central-dual: that treats the arithmetic action SL_3(Z[1/p]) on cosets of SL_3(Z) and refutes the large-prime central-dual inequality; this treats SL_3(Z) on cosets of its explicit thin subgroup and refutes the selected modulus for the thin HNN route.
  stable-finite-actions-blocks-codense-kazhdan-coset-soficity: that supplies a conditional theorem proving nonsoficity from stability in finite actions; this records the opposite implication from a sofic atlas to a matrix-ultraproduct counterexample.
---

Put

```text
A=SL_3(Z),  C=<a,b>,  X=A/C.
```

If the action `A curvearrowright X` is sofic, then
`thin-selected-module-is-profinite-continuous` is false.  More precisely,
there is a tracial matrix-ultraproduct representation of `A` and a selected
`C`-central unitary `v` whose cyclic conjugation module is
`lambda_(A/C)`, hence is not weakly contained in `pi_FD^0`.

Therefore the new selected modulus already implies nonsoficity of the thin
coset action.  It is not merely a repackaging of the exact
finite-dimensional co-density theorem: every exact finite action collapses
the coset atlas, while a hypothetical positive sofic atlas would directly
manufacture the forbidden selected module.
