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
- The complete 2026-08-24 source audit is now
  `current-nonce-sources-do-not-supply-a-finite-cocycle-sector`.  In the
  Manzoor lane, `zero-one-irs-character-is-normal-dirac` shows that removing
  every intermediate native coefficient would make the IRS a normal Dirac
  mass and already produce the desired quotient group.  CDI transfers rather
  than creates this projective-word gate, while MIP-star/BCS provides no
  unrelated projective basis.  Thus finite-image cocycle extraction is not
  latent in the current data.
- **Irrational twists (2026-09-13, idea lane `nh-undecidable-J`, approach
  5).** Moving the central character off the roots of unity gives no escape.
  - For finitely presented `Gamma`,
    `torsion-dense-schur-multiplier-compiles-twisted-nonce` already turns a
    non-CE twist at any phase into a non-CE torsion twist and a non-hyperlinear
    finite central extension.
  - `ce-twist-set-is-a-hecke-stable-closed-subgroup` shows the connected CE part
    is a rational subtorus.
  - Irrational rotation relations `uv = e(theta)vu` only generate twisted
    algebras of abelian groups, which are amenable and hence CE.
  - So the separation still needs a non-amenable carrier with a projective
    basis.
- **Honest MIP-star strategies as one fixed twisted factor (2026-09-13).** The
  honest synchronous strategies of the Culf--Mastel / DFNQXY constructions
  (Pauli and Weyl--Heisenberg packets) are exact representations of finite
  groups. Their limits factor through twisted group algebras of locally finite
  groups, and those are CE.  Factoring a non-CE trace through one fixed
  `L_omega(Gamma)` therefore needs a non-amenable `Gamma` with the same
  projective-word basis, which is this node again.
- **Hecke structure on the `Gamma(4)` twist torus (2026-09-13).**
  `ce-twist-set-is-a-hecke-stable-closed-subgroup` proves that the CE Lie
  algebra `W(Gamma(4))`, a subspace of `R^118`, is rational and Hecke-stable,
  and that it is all of `R^118` iff every finite cyclic central cover of
  `Gamma(4)` is hyperlinear.  This is structure, not a mechanism: any proof
  that `W != R^118` is itself a non-CE theorem.

## Route hygiene

- Finite generation of the projective quotient is not an additional gate:
  Connes embeddability is local under increasing weakly dense unions, so a
  non-CE twist already fails on one finitely generated subgroup.
- What cannot be imported for free is a multiplication-closed orthonormal
  projective basis.  Supplying it is equivalent to supplying the desired
  nonhyperlinear group.
