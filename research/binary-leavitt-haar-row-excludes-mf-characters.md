---
rg: 2
id: binary-leavitt-haar-row-excludes-mf-characters
kind: route
title: Diracize a nontrivial MF character to the full Haar root profile
target: binary-leavitt-steinberg-mf-characters-are-trivial
requires:
  - binary-leavitt-haar-row-profile-is-not-mf-character-restriction
  - character-diracization-limit
  - binary-leavitt-full-row-elements-normally-generate
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
generates `Delta` by
`binary-leavitt-full-row-elements-normally-generate`: one transverse
commutator isolates a nonzero coefficient root, whose normal closure is the
whole group.  This is purely algebraic and does not use the quantitative
corona-rank theorem.  Therefore `K intersect N={1}`.  It follows that

```text
1_K|_N=delta_1,
```

the Fourier transform of full Haar measure on `hat N`.  This contradicts the
first prerequisite.  Hence every MF character is trivial.
