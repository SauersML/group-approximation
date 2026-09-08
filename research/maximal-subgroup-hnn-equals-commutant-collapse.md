---
rg: 2
id: maximal-subgroup-hnn-equals-commutant-collapse
kind: claim
title: A maximal-subgroup centralizer HNN group is nonhyperlinear exactly when all canonical actor commutants collapse
distinct_from:
  hnn-route-is-relative-commutant-collapse: That gives sufficiency of the collapse identity on canonical HNN models; this proves equivalence with collapse in every canonical actor embedding under ordinary subgroup maximality.
  relative-embedding-is-commutant-separation: That needs a family separating every outside group element; maximality here makes any single commutant leak have exactly the required stabilizer.
artifacts:
  - research/artifacts/commutation-stabilizer-relative-embedding-2026-09-07.md
---

Let `C` be a maximal proper subgroup of a countable group `A`, and put
`H=A *_C(C x Z)`. Then `H` is nonhyperlinear if and only if

```text
pi(L(C))' cap Q = pi(L(A))' cap Q
```

for every canonical trace-preserving embedding `pi:L(A)->Q` into a
tracial matrix ultraproduct.

A failure of this identity yields a `C`-central spectral projection
whose commutation stabilizer is proper in `A`. Maximality makes that
stabilizer exactly `C`, so tensor extraction gives a scalar relative
embedding and therefore a canonical HNN model. Conversely a canonical
free binary coset lamp supplies a commutant leak whenever `H` is
hyperlinear.

The construction may change the embedding and enlarge the
ultraproduct. It does not turn the original projection into a Haar
letter in the same model. Maximality means maximal among all proper
subgroups; no maximality statement for a named arithmetic subgroup is
included in this theorem.
