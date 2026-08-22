---
rg: 2
id: recursive-twisted-factor-higman-compiler
kind: claim
title: An effective non-CE twist compiles into a finitely presented nonhyperlinear group
distinct_from:
  torsion-dense-schur-multiplier-compiles-twisted-nonce: that compiler approximates the multiplier by a torsion class to obtain a finite central extension; this compiler instead uses the relation-centralizing extension and Higman embedding, requiring effectivity but no torsion or finite presentation of the projective quotient.
  nonce-twisted-factor-gives-nonhyperlinear-group: that compiler produces a countable phase-range extension without guaranteeing a recursive or finite presentation; this one preserves enough effectivity for Higman embedding.
---

Let `F=F(x_1,...,x_n)`, let `N normal F` be the normal closure of a
recursively enumerable set of words, and put `Gamma=F/N`.  Suppose a scalar
multiplier `omega` on `Gamma` has non-Connes-embeddable twisted group factor
`L_omega(Gamma)`.  Then

```text
E = F/[F,N]
```

is a finitely generated recursively presented nonhyperlinear group.  Hence
`E` embeds in a finitely presented nonhyperlinear group.

Concretely, if `R` recursively normally generates `N`, a recursive
presentation for `E` is

```text
< x_1,...,x_n | [x_i,r]=1  (1<=i<=n, r in R) >.          (RTH1)
```

Thus an effective projective-basis realization of a non-CE factor does not
need finite phases, a residually finite Schur multiplier, or a finitely
presented projective quotient in order to yield a finitely presented
nonhyperlinear group.

