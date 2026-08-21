---
rg: 2
id: finite-symmetry-equivariant-edge-proof
kind: route
title: Extend the edge map to the semidirect product and use one stable word
target: finite-symmetry-equivariant-edge-has-one-holonomy
requires:
  - finite-schur-clifford-packet-flexible-hs-exactification
  - finite-group-shared-overlap-polar-alignment
---

Equivariance makes `(FSE1)` a homomorphism: multiplication in the two
semidirect products is preserved because
`phi(h.e)=h.phi(e)`.  It is injective because `phi` is.  The HNN normal-form
theorem therefore embeds the base and supplies `(FSE2)` with one stable
letter.

For `h in H`, `(FSE2)` sends `(1,h)` to itself, so `t` commutes with `h`.
Conjugating the base relation for `p` by `h` proves `(FSE4)`.  In an exact
isotypic decomposition, Schur's lemma permits a multiplicity unitary, but it
belongs to the single operator representing `t`; its orbit transports are
conjugates, not independent choices.

For an approximate tuple, exactify the two fixed finite semidirect tables and
align their shared edge action.  Every group-algebra spectral projection in
the statement is a fixed finite linear combination of packet words.  Fixed
word telescoping, the stable-letter relators, and polar alignment therefore
give `(FSE5)` with a constant depending only on the two finite tables.  Trace
invariance under the exactified `H` action then gives the asserted common
orbit marginals.
