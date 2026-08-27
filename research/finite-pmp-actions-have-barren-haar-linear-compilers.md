---
rg: 2
id: finite-pmp-actions-have-barren-haar-linear-compilers
kind: claim
title: Every finite pmp action has a Haar-linear factor compiler, but its crossed product is CE
distinct_from:
  haar-algebraic-actions-have-permutation-koopman-spectrum: that gives a necessary spectral condition for arbitrary action factors; this constructs an explicit Haar finite-field factor for every finite p.m.p. action and identifies why it cannot carry non-CE data.
  dense-homoclinic-algebraic-actions-are-ce: that proves CE from dense homoclinic points for broad profinite actions; this finite-factor construction has finite actor image and is CE by an elementary group-extension argument.
  algebraic-compact-action-envelope-for-non-ce-relation: that needs the full finite non-CE moment obstruction, including normalizer multiplication; this compiles exactly the finite invariant base partition and proves that such data alone is barren.
---

Let a countable sofic group `H` act measure-preservingly on a finite
probability space `(X,mu)`, and fix a prime `p`.  There is a compact
second-countable abelian `F_p`-group `K`, with Haar measure and an algebraic
`H`-action, together with a measurable equivariant measure-preserving factor

```text
pi:(K,Haar) -> (X,mu).                                  (FHC1)
```

The action `H -> Aut(K)` can be chosen to have the same finite image as the
permutation action on `X`.  Hence, writing `A=K-hat`,

```text
A rtimes H
```

is sofic and `L^infinity(K) rtimes H` is Connes embeddable.  Pullback along
`pi` gives a trace-preserving inclusion

```text
L^infinity(X) rtimes H -> L^infinity(K) rtimes H.       (FHC2)
```

Consequently every **finite `H`-invariant Boolean algebra of measurable
sets** can be encoded exactly in a Haar finite-field algebraic action, but
this compiler can never preserve a finite non-CE moment obstruction as a
whole.  For `H=SL_3(Z)`, any direct partition compiler that closes after
finitely many translates lands in this CE case.  A viable relation-to-module
compiler must use the infinite translate closure and must encode the
relation normalizers there; finite invariant partition probabilities are not
the missing datum.
