---
rg: 2
id: sl3-collapse-via-global-adjoint-temperedness
kind: route
title: Make the whole adjoint complement tempered and apply the selected-vector collapse lemma
target: sl3-large-prime-pair-relative-commutant-collapse
requires:
  - tempered-selected-conjugation-vector-obeys-rcc
---

**INVALIDATED PROPOSAL.**  The proposed proof was to show that, for every
canonical arithmetic matrix embedding, the entire orthogonal complement of
the group-factor copy in the conjugation representation is weakly contained
in the regular representation.  Every lattice-central leak would then have
a tempered selected cyclic module, and
`tempered-selected-conjugation-vector-obeys-rcc` would force it to be
S-arithmetic-central.

This global spectral premise is false even on the already-correct exact
congruence face.  A fixed nontrivial finite quotient contributes its
mean-zero Koopman representation to the adjoint complement of a residual
congruence embedding.  Its finite-index kernel acts trivially, so it is not
weakly contained in the regular representation.  This is the counterexample
`canonical-congruence-adjoint-complement-is-not-tempered`.

The counterexample does not refute selected-vector temperedness: profinite
co-density prevents that finite-quotient sector from containing a
`Lambda`-fixed mean-zero vector.  Hence the live spectral alternative is the
strictly narrower selected cyclic-module statement; the invalidated route is
the attempted promotion from matrix origin to global adjoint temperedness.

