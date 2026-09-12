---
rg: 2
id: stw74-cartan-clopen-compression-proof
kind: route
title: Turn a Cartan cutdown into an invertible clopen corner
target: stw74-zero-dimensional-cartan-forces-property-sp
requires:
  - stw74-property-sp-is-the-exact-missing-condition
artifacts:
  - research/artifacts/stw74-zero-dimensional-cartan-sp-audit-2026-08-30.md
---

Let `E:A->D` be the faithful Cartan expectation.  We first record the
standard topologically-principal cutdown in the exact form needed below.

## Cartan cutdown

For every `0!=a in A_+` and every `epsilon>0`, there is a positive
contraction `f in D` such that

```text
||f a f-f E(a) f||<epsilon,
||f E(a) f||>||E(a)||-epsilon.                         (CC1)
```

Here is the finite-support proof, including the twisted case.  Renault's
reconstruction realizes the Cartan pair as

```text
(A,D) ~= (C*_r(G,Sigma), C(X)),
```

where `G` is a second-countable locally compact Hausdorff topologically
principal etale groupoid, `Sigma` is its twist, and `X=G^(0)`.  Approximate
`a` by a compactly supported twisted section and cover its support by
finitely many open bisections.  Choose a unit with trivial isotropy in an
open set on which `E(a)` is within `epsilon` of its norm.  For each of the
finitely many off-unit bisection pieces, the associated partial
homeomorphism does not return this unit to itself.  Shrinking a common unit
neighbourhood makes its source and range pieces disjoint.  The pieces which
meet the unit space contribute their diagonal restriction; after subtracting
that restriction, continuity makes their remaining compression arbitrarily
small.  Choose `f in C_c(X)_+`, supported in the common neighbourhood and
equal to one at the selected unit.  Multiplication by `f` on the two sides
kills the separated bisection pieces and controls the remaining
approximation error, giving `(CC1)`.  A twist only replaces scalar functions
on a bisection by local line-bundle sections; the source/range support
calculation is identical.

For an untwisted groupoid this is exactly Brown--Clark--Sierakowski, Lemma
3.1.  The preceding finite-bisection proof also shows directly that neither
amenability nor an untwisted presentation is being inserted.

## Create a clopen spectral gap

Fix `0!=a in A_+` and put

```text
d=E(a),                 M=||d||>0.
```

The strict inequality follows from faithfulness of `E`.  Apply `(CC1)` with
`0<epsilon<M/8`, obtaining `f`.  Since

```text
||f d f||>M-epsilon,
```

there is a point `x in X` at which `f(x)^2 d(x)>M-epsilon`.  By continuity
and zero-dimensionality, there are a nonempty clopen neighbourhood `V` of
`x` and a number `t>0` such that, for `p=1_V in D`,

```text
p f d f p >= (M-2 epsilon)p,          p f p >= t p.     (CC2)
```

The clopen set is compact because `X` is compact, so `p` is a projection of
`D subset A`.  Compressing `(CC1)` by `p` and using `(CC2)` gives

```text
p f a f p >= (M-3 epsilon)p.                         (CC3)
```

Inside the unital corner `pAp`, put `g=pfp`.  It is invertible there by the
second inequality in `(CC2)`, and

```text
p f a f p = g (p a p) g.
```

Equation `(CC3)` makes the left side invertible in `pAp`; conjugating by
`g^(-1)` shows that `pap` is invertible in `pAp`.

## Move the clopen projection into the hereditary algebra

Let `y=a^(1/2)p`.  Since `y*y=pap` is invertible in `pAp`,

```text
v=y(pap)^(-1/2)
```

is a partial isometry with `v*v=p`.  Its range projection

```text
q=vv*=a^(1/2) p (pap)^(-1) p a^(1/2)
```

is nonzero and belongs to `Her_A(a)`.  Every nonzero hereditary subalgebra
contains `Her_A(a)` for some nonzero positive `a`, so `A` has property (SP).

If `A` also satisfies the projection hypothesis of Problem LXXIV, the
established equivalence `stw74-property-sp-is-the-exact-missing-condition`
now makes `A` purely infinite.
