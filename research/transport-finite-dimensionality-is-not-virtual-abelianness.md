---
rg: 2
id: transport-finite-dimensionality-is-not-virtual-abelianness
kind: claim
title: The finite-dimensionality hypothesis in transport cannot be weakened to a virtually abelian orbit group
distinct_from:
  finite-block-coordinates-share-one-mf-image: that is a proved consequence of finite-dimensional transport; this records a proposed virtually abelian counterexample whose full construction is not present in the cited source.
artifacts:
  - non_mf_groups_exist.tex
---

**OPEN: construction missing from the current source.** The target is the
following proposed counterexample. Let `Gammabar = Z^3 x| SL_3(Z)`,
let `alpha(v, A) = (2v, A)`, and let `V`
be the ascending HNN extension of `Gammabar` along `alpha`.  There is an
injective homomorphism `sigma` of `V` into the unitary group of a norm
matrix corona for which:

1. there is a unital **commutative** subalgebra `Acal ~= C(T)`, normalized
   by `sigma(Gammabar)`, where `T` is a wedge of eight arcs;
2. an element of `Acal` fixed by `sigma(t Gammabar t^(-1))` is **not** fixed
   by `sigma(Gammabar)`.

Such a construction would show that finite-dimensionality cannot simply
be replaced by commutativity. A separate proposed strengthening uses an
order-two element with finite orbit generating `Z^7 x| C_2`. It cannot
be the same witness inside `C(T)`: this algebra is commutative, and its
connected spectrum forces every order-two unitary to be the constant
`1` or `-1`. The stronger virtually abelian witness therefore requires
a different ambient algebra and a separate construction.

## The elementary half

Even the crude form of the obstruction is worth recording: a rank-one
projection in `M_d(C)` has operator norm `1` and normalized
Hilbert-Schmidt norm `d^(-1/2)`.  So on a summand whose relative size tends
to zero, equivalence of norms on a fixed finite-dimensional algebra gives
nothing uniform.  This is what the rank bound in the transport proof
supplies instead.

## A correction to an earlier write-up

`alpha(Gammabar) = 2Z^3 x| SL_3(Z)` is **not normal** in `Gammabar`:
conjugating `(0, A)` by a translation `w` has translation part `w - Aw`,
which need not be even — take `A = e_12` and `w = (0,1,0)`, giving
`(-1,0,0)`.  So `Gammabar / alpha(Gammabar)` is a coset space, not a
quotient group, and the action on the eight generators factors through the
reduction `Gammabar -> F_2^3 x| SL_3(F_2)`.

## Attempts and missing proof

The previous write-up said the construction had been removed from the
manuscript. The current cited manuscript contains the finite-dimensional
transport theorem and the rank estimate above, but supplies neither
the wedge-of-arcs corona realization nor the separate involution
realization. Those elementary observations do not prove either
counterexample. A complete construction must specify the algebra,
the action, the corona map, its injectivity, and the element witnessing
failure of fixed-point transport. No proof route is asserted here.
