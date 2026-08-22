---
rg: 2
id: length-four-kl-fence-for-leavitt-equations
kind: claim
title: A Leavitt Kervaire--Laudenbach candidate with full coefficient support must have variable length at least five
distinct_from:
  three-root-asymmetric-kl-word-has-finite-core-pushout: That particular length-three word is protected by a finite-core pushout; this is the coefficient-independent theorem that protects every nonsingular word of length at most four, even when its coefficients generate the whole Leavitt group.
  leavitt-degree-kernel-normally-generated-by-one-word: That asks for a successful normal generator at arbitrary length; this gives a sharp proven lower bound on the search length and the complete sign patterns at the first unresolved length.
  kervaire-laudenbach-holds-for-hyperlinear: That protects equations over coefficient groups already known hyperlinear at every length; this protects all coefficient groups, including the binary Leavitt group whose hyperlinearity is in question, but only through length four.
---

Let `G=L_(F_2)(1,2)^x`, and write a cyclically reduced one-variable word as

```text
w=g_0 t^(e_1) g_1 ... t^(e_k) g_k,       e_i != 0.
```

Its variable length is `ell_t(w)=sum_i |e_i|`.  If `deg_t(w) != 0` and
`ell_t(w) <= 4`, then the coefficient map

```text
G -> (G*<t>)/<<w>>
```

is injective.  This remains true if the finite coefficient support
`{g_0,...,g_k}` generates all of `G`; finite-core localization is not being
used.

Consequently every Leavitt equation capable of witnessing nonhyperlinearity
through Kervaire--Laudenbach must have `ell_t(w) >= 5`.  At the first possible
length, parity gives

```text
deg_t(w) in {+-1,+-3,+-5}.
```

The `+-5` patterns have only one sign and are covered by the classical
positive-equation theorem.  Thus the first genuinely unfenced full-support
search consists of mixed-sign length-five words: up to inversion, cyclic rotation, and
replacing `t` by `t^(-1)`, their signs have type `++++-` (degree `3`) or
`+++--` (degree `1`).  No coefficient choice, simplicity argument, or
self-similarity can make a shorter word work.

This is a search fence, not a length-five solution: the published length-five
results impose additional coefficient restrictions and do not establish the
unrestricted case.
