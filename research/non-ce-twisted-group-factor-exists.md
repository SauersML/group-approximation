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

`twisted-factor-existence-is-equivalent-to-nonhyperlinearity` proves the
converse with the trivial cocycle and also proves that any bad countable twist
restricts to a bad finitely generated twisted subgroup.  Therefore this node
is **exactly equivalent to the root goal**.  It must not be counted as an
independent bridge toward that goal: proving a projective basis for a known
non-CE relation/game algebra already constitutes the complete breakthrough.

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

## Route hygiene

- Finite generation of the projective quotient is not an additional gate:
  Connes embeddability is local under increasing weakly dense unions, so a
  non-CE twist already fails on one finitely generated subgroup.
- What cannot be imported for free is a multiplication-closed orthonormal
  projective basis.  Supplying it is equivalent to supplying the desired
  nonhyperlinear group.
