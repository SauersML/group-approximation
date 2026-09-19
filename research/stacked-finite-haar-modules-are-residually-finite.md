---
rg: 2
id: stacked-finite-haar-modules-are-residually-finite
kind: claim
title: A countable product of finite invariant Haar modules has residually finite dual semidirect product
distinct_from:
  finite-pmp-actions-have-barren-haar-linear-compilers: that treats one finite invariant probability algebra and chooses an actor action with finite image; this allows countably many finite invariant linear factors, an infinite total actor image, and a generating infinite Fourier-binary label family.
  dense-homoclinic-algebraic-actions-are-ce: that uses density of homoclinic points and sofic model measures; the product actions here can have trivial homoclinic group, and residual finiteness follows instead from invariant finite-coordinate quotients.
  finite-type-linear-vfree-envelope-is-residually-finite: that uses finite presentation over a virtually free group ring; this applies to an arbitrary residually finite actor, including `SL_3(Z)`, and imposes no finite-type hypothesis.
---

Let `H` be a residually finite countable group.  For each `n>=1`, let `K_n`
be a finite abelian group equipped with an action of `H` by automorphisms, and
let

```text
K = product_(n>=1) K_n
```

with the coordinatewise `H`-action and product Haar measure.  Then, writing
`A=K-hat`,

```text
A rtimes H
```

is residually finite.  Consequently

```text
L^infinity(K,Haar) rtimes H = L(A rtimes H)
```

is Connes embeddable.

Equivalently, suppose a proposed Haar-linear recoding is obtained by stacking
countably many finite `H`-invariant Haar-linear label systems independently.
Even if their union generates the entire probability algebra and the product
action of `H` has infinite image, the resulting algebraic compact-action
envelope is barren.

In particular this applies to `H=SL_3(Z)`.  Thus the Fourier-binary criterion
`infinite-label-process-is-haar-linear-iff-fourier-binary` cannot be met by
successively adjoining independent finite invariant compilers.  A native
non-CE Haar-linear `SL_3(Z)` action must have genuinely nonsplit infinite
linear dependence between the layers: its dual module cannot be a direct sum
of finite invariant modules.

