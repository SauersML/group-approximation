---
rg: 2
id: effective-twisted-factor-equivalence-proof
kind: route
title: Apply the relation-centralizing compiler and reverse it with the trivial twist
target: effective-twisted-factor-existence-is-equivalent-to-fp-nonhyperlinearity
requires:
  - recursive-twisted-factor-higman-compiler
  - higman-bypass-needs-only-fg-recursive-nonhyperlinear
  - thom-central-corner-criterion
---

Let `(ET)`, `(RP)`, and `(FP)` denote clauses 1, 2, and 3.

`(ET) => (RP)` is `recursive-twisted-factor-higman-compiler`.  If
`Gamma=F/N` carries the bad twist, the group

```text
E=F/[F,N]
```

is nonhyperlinear and has the recursive presentation

```text
<x_1,...,x_k | [x_i,r]=1 for 1<=i<=k and r in R>,
```

where `R` recursively normally generates `N`.

For `(RP) => (ET)`, write the finitely generated recursively presented group
as `H=F/N` with `F` of finite rank and `N` recursively normally generated.
Take `omega=1`.  Since

```text
H hyperlinear  iff  L(H) is Connes embeddable,
```

nonhyperlinearity of `H` makes `L_1(F/N)` non-CE, giving `(ET)`.

`(FP) => (RP)` is immediate.  Finally `(RP) => (FP)` is
`higman-bypass-needs-only-fg-recursive-nonhyperlinear`: Higman's embedding
theorem embeds the recursively presented group in a finitely presented one,
and subgroup heredity of hyperlinearity makes the ambient group
nonhyperlinear.  This proves all three equivalences.

