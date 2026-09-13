---
rg: 2
id: thompson-f-not-amenable-from-cstar-simple-disjoint-pair
kind: route
title: A C*-simple subgroup of T with a disjointly supported pair would make Thompson's group F non-amenable
target: thompson-f-is-not-amenable
requires:
  - thompson-t-has-cstar-simple-subgroup-with-disjoint-pair
  - thompson-t-disjoint-pair-cstar-simple-subgroup-criterion
---

Immediate: apply `thompson-t-disjoint-pair-cstar-simple-subgroup-criterion` to the witness
subgroup given by `thompson-t-has-cstar-simple-subgroup-with-disjoint-pair`.
