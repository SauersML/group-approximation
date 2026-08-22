---
rg: 2
id: length-five-kl-fence-for-leavitt-equations
kind: claim
title: A Leavitt Kervaire--Laudenbach candidate with full coefficient support must have variable length at least six
distinct_from:
  three-root-asymmetric-kl-word-has-finite-core-pushout: That particular length-three word is protected by a finite-core pushout; this is the coefficient-independent theorem that protects every nonsingular word of length at most five, even when its coefficients generate the whole Leavitt group.
  leavitt-degree-kernel-normally-generated-by-one-word: That asks for a successful normal generator at arbitrary length; this gives the sharp published lower bound on the search length and the complete sign patterns at the first unresolved length.
  kervaire-laudenbach-holds-for-hyperlinear: That protects equations over coefficient groups already known hyperlinear at every length; this protects all coefficient groups, including the binary Leavitt group whose hyperlinearity is in question, but only through length five.
---

Let `G=L_(F_2)(1,2)^x`, and write a cyclically reduced one-variable word as

```text
w=g_0 t^(e_1) g_1 ... t^(e_k) g_k,       e_i != 0.
```

Its variable length is `ell_t(w)=sum_i |e_i|`.  If `deg_t(w) != 0` and
`ell_t(w) <= 5`, then the coefficient map

```text
G -> (G*<t>)/<<w>>
```

is injective.  This remains true if the finite coefficient support
`{g_0,...,g_k}` generates all of `G`; finite-core localization is not being
used.

In particular, both first length-five mixed-sign shapes proposed for the
Leavitt search are impossible:

```text
++++-     (degree 3),
+++--     (degree 1).
```

No choice of prefix-self-similar coefficients, even a choice generating all
of `G`, can make either relative quotient kill a coefficient.

Consequently every Leavitt equation capable of witnessing nonhyperlinearity
through Kervaire--Laudenbach must have `ell_t(w) >= 6`.  At length six,
parity gives absolute degrees `2,4,6`.  The degree-six patterns have only one
sign and are covered by the positive-equation theorem.  Thus, up to inversion,
cyclic rotation, and replacing `t` by `t^(-1)`, the first genuinely unfenced
full-support sign types are

```text
+++++-    (five positive, one negative; degree 4),
++++--    (four positive, two negative; degree 2).
```

This is a search fence, not a length-six solution.  The available general
length-six theorems require torsion-free coefficients, while the binary
Leavitt unit group has explicit involutions.

