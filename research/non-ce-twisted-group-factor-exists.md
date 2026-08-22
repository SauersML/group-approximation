---
rg: 2
id: non-ce-twisted-group-factor-exists
kind: claim
title: A non-Connes-embeddable twisted group factor exists
---

There are a countable group `Gamma` and a scalar multiplier
`omega in Z^2(Gamma,T)` such that `L_omega(Gamma)` is not Connes embeddable.

By `nonce-twisted-factor-gives-nonhyperlinear-group`, any witness immediately
produces the explicit countable nonhyperlinear central extension
`<range(omega)> x_omega Gamma`.  The unresolved content is therefore only the
projective-basis realization of one non-CE tracial factor; finite phases and
Schur-multiplier separation are not part of the root gate.

## Attempts

- Apply the projective-word characterization to the fixed CDI/Manzoor
  non-CE factor.  The source generators have intermediate trace words, and
  no replacement projective unitary basis is known.
- Orthogonalize a non-CE character by tensor powers or free labels.  This
  forces non-scalar word traces to zero but also erases the payload; adjoining
  enough labels to recover the payload recreates the intermediate trace word.
- Groupify the finite non-CE BCS algebra.  Current finite phase packets do not
  exclude forbidden selector sectors, so they do not preserve the robust
  finite-dimensional energy gap.
