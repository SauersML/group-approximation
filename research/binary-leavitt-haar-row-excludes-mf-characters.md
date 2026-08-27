---
rg: 2
id: binary-leavitt-haar-row-excludes-mf-characters
kind: route
title: Diracize a nontrivial MF character to the full Haar root profile
target: binary-leavitt-steinberg-mf-characters-are-trivial
requires:
  - binary-leavitt-haar-row-profile-is-not-mf-character-restriction
  - character-diracization-limit
  - binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale
---

Suppose `chi` is a nontrivial MF character of `Delta` and put

```text
K={g in Delta:|chi(g)|=1}.
```

The character-diracization lemma gives characters
`|chi|^(2k)->1_K`.  These remain MF characters: fixed conjugate tensor powers
of operator-norm asymptotic representations are still operator-norm
asymptotic, and a diagonal choice over the tensor exponent and the matrix
coordinate realizes the pointwise limit.

The Steinberg group is perfect directly from its root commutator relations.
Hence `K=Delta` would make the GNS representation scalar and force `chi=1`,
contrary to assumption.  Thus `K` is proper.

Every nonidentity element of a full row or column root module normally
generates `Delta`.  Commute it with a suitable transverse elementary root to
isolate one nonzero coefficient root; the uniform root-normal-word theorem
then reaches the marked root, which normally generates the group.  Therefore
`K intersect N={1}`.  It follows that

```text
1_K|_N=delta_1,
```

the Fourier transform of full Haar measure on `hat N`.  This contradicts the
first prerequisite.  Hence every MF character is trivial.
