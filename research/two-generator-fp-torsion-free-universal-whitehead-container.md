---
rg: 2
id: two-generator-fp-torsion-free-universal-whitehead-container
kind: claim
title: A two-generator finitely presented torsion-free group universally injects connective Whitehead groups
distinct_from:
  higher-whitehead-universal-finitely-presented-torsion-free-group: that proves the universal higher-Whitehead property without controlling the number of generators or recording approximation-theoretic hardness; this compresses its witness to two generators and makes it simultaneously nonsofic and non-MF.
  whitehead-universal-finitely-presented-container: that contains all recursively presented groups but necessarily has every finite torsion order; this host is torsion-free and is universal only for torsion-free inputs.
  whitehead-injective-two-generator-recursive-compression: that compresses one input group and records only ordinary Whitehead injectivity; this chooses one fixed input-independent host and controls every connective Whitehead degree.
---

There exists a two-generator finitely presented torsion-free group `E` such
that every countably generated recursively presented torsion-free group `K`
has an embedding

```text
K -> E
```

which, simultaneously for every `i>=0`, induces an injection

```text
Wh_i(K) -> Wh_i(E).
```

Here `Wh_i(G)=pi_i Wh_Z(G)` is Waldhausen's connective Whitehead group.
The same `E` can be chosen to be both nonsofic and non-MF.

**ESTABLISHED 2026-08-30** by
[[two-generator-universal-whitehead-container-proof]].
