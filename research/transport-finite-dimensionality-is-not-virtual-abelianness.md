---
rg: 2
id: transport-finite-dimensionality-is-not-virtual-abelianness
kind: claim
title: The finite-dimensionality hypothesis in transport cannot be weakened to a virtually abelian orbit group
distinct_from:
  finite-block-coordinates-share-one-mf-image: that is a positive consequence of the finite-dimensional transport theorem for genuinely finite blocks; this is a counterexample showing the finiteness hypothesis in that theorem cannot be relaxed.
artifacts:
  - non_mf_groups_exist.tex
---

Let `Gammabar = Z^3 x| SL_3(Z)`, let `alpha(v, A) = (2v, A)`, and let `V`
be the ascending HNN extension of `Gammabar` along `alpha`.  There is an
injective homomorphism `sigma` of `V` into the unitary group of a norm
matrix corona for which:

1. there is a unital **commutative** subalgebra `Acal ~= C(T)`, normalized
   by `sigma(Gammabar)`, where `T` is a wedge of eight arcs;
2. an element of `Acal` fixed by `sigma(t Gammabar t^(-1))` is **not** fixed
   by `sigma(Gammabar)`.

So a finite subgroup cannot be replaced in the finite-dimensional transport
theorem of `non_mf_groups_exist.tex` by a finitely generated virtually
abelian one, even when the distinguished element has order two and a finite
orbit.  The orbit group in the witness is `Z^7 x| C_2`.

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

**Status.**  Proved and written out; removed from
`non_mf_groups_exist.tex` on 2026-09-08 as settling a secondary optimality
question that no retained construction uses.
