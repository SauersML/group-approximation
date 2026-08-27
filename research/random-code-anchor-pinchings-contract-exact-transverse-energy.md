---
rg: 2
id: random-code-anchor-pinchings-contract-exact-transverse-energy
kind: claim
title: Random code-coordinate pinchings contract exact-base transverse energy by code distance
distinct_from:
  joint-pinching-costs-linear-generator-gap: that compares averaged generator commutators with one full joint pinching and loses the number of generators; this averages single-coordinate pinchings and uses the code distance to obtain a constant spectral gap on exact code-character blocks.
  code-laplacian-has-uniform-cp-green-approximants: that constructs finite CP approximants to an inverse adjoint Laplacian; this is the elementary Markov contraction which underlies a possible random-anchor iteration.
  balanced-overlay-local-alternating-projections-contract: that proves local contraction after the tuple is already in an operator tube; this identifies the exact-base global anchor contraction and its same-Hilbert reflection-rounding cost.
---

ESTABLISHED.  Let `C<=F_2^L` have relative distance at least `delta`, and
let `S_1,...,S_L` be an exact commuting reflection representation whose
joint characters belong to `C`.  Write `(p_x)_(x in C)` for its joint PVM,
allowing arbitrary multiplicities, and

```text
E(T)=sum_x p_x T p_x,
Phi_a(T)=(T+S_a T S_a)/2.                               (RAP1)
```

For every `T in L_2(M)` with `E(T)=0`, a uniformly random coordinate `a`
satisfies

```text
E_a ||Phi_a(T)||_2^2 <= (1-delta)||T||_2^2.              (RAP2)
```

For independent uniform anchors `a_1,...,a_k`, the commuting composition
obeys

```text
E ||Phi_(a_k)...Phi_(a_1)(T)||_2^2
 <= (1-delta)^k ||T||_2^2.                              (RAP3)
```

These estimates are dimension-free, completely amplified, and insensitive
to the ranks of the `p_x`.

Indeed decompose `T=sum_(x,y) p_x T p_y`.  On the `(x,y)` block, `Phi_a`
has multiplier `1_(x_a=y_a)`.  The condition `E(T)=0` removes `x=y`, while
every remaining difference `x+y` is a nonzero codeword and therefore has
weight at least `delta L`.  Orthogonality of the blocks proves `(RAP2)`;
independence proves `(RAP3)`.

There is also a same-Hilbert nonlinear one-anchor operation with a sharp
dimension-free cost.  For arbitrary reflections `A,B`, put

```text
X=Phi_A(B),
B'=sgn(X),                                                (RAP4)
```

where the value of the sign on the zero spectral subspace is chosen inside
the commutant of `A`.  Then `B'` is a reflection commuting with `A` and

```text
||B-B'||_2^2 <= (1/2)||[A,B]||_2^2.                     (RAP5)
```

To prove this, pinching is the orthogonal projection onto the commutant of
`A`, hence

```text
||B-X||_2^2=(1/4)||[A,B]||_2^2=tr(1-X^2).
```

Scalar functional calculus gives
`||X-sgn(X)||_2^2<=tr(1-X^2)`.  The two differences are orthogonal (the
first is off-diagonal for `A`, the second diagonal), yielding `(RAP5)`.
Thus pinching all reflections against one selected anchor and
reflection-rounding costs at most one half of that anchor's total
commutator energy.  Previously installed anchors remain exact: a new anchor
chosen from their common commutant has a pinching preserving that
commutant, and functional calculus stays inside it.

The result supplies the desired constant contraction at an exact code base
and a controlled nonlinear implementation of each anchor.  It does **not**
identify an exact code base for a diffuse approximate tuple; that missing
promotion is isolated in
`random-anchor-contraction-does-not-yet-enter-the-diffuse-basin`.
