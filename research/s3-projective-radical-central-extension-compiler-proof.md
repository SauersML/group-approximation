---
rg: 2
id: s3-projective-radical-central-extension-compiler-proof
kind: route
title: Cut the finite central character and separate exact invisibility from HS collapse
target: s3-projective-radical-central-extension-has-exact-robust-fork
requires:
  - agent-aggregate-escape-two-intertwiner-clifford-dichotomy
  - finite-central-hs-sector-decomposition
  - agent-aggregate-escape-two-intertwiner-aco4-is-twisted-nonce
  - exact-fd-invisibility-has-no-general-hs-robustification
  - thom-central-corner-criterion
---

The finite packet has finitely many irreducible types, so the stabilizer of
one type has finite index in the finitely presented actor.  Finite-index
subgroups of finitely presented groups are finitely presented.  The action on
the finite packet factors through a finite automorphism group.  Choose one
intertwiner for each element of that finite image.  Its multiplier is a
cocycle on a finite group.  After changing the intertwiners by scalar phases,
the cocycle may be chosen finite-valued: pull the projective representation
back to a finite Schur cover, or equivalently use that `H^2(A,T)` is finite
for finite `A` and choose a root-of-unity representative.  This gives
`(SCR2)`.  A finite extension of a finitely presented group is finitely
presented.

In a representation of `E_sigma` with `z` acting by its tautological scalar,
the multiplication law in `(SCR2)` says exactly that the quotient lifts obey
the inverse multiplier `omega^(-1)`.  Conversely, any inverse-projective
stabilizer representation extends by the prescribed scalar action of
`mu_m`.  This proves the exact representation correspondence.

It cannot prove nonhyperlinearity.  The group and central involution in
`exact-fd-invisibility-has-no-general-hs-robustification` satisfy the same
exact conclusion but the group is sofic.  Its canonical matrix microstates
keep the central involution at regular distance from the identity.  This is a
literal counterexample to every general exact-to-HS promotion needed in
`(SCR3)`.

Now assume `(SCR4)` and suppose `E_sigma` were hyperlinear.  Choose canonical
matrix microstates.  Since `mu_m` is finite and central,
`finite-central-hs-sector-decomposition` changes them by `o(1)` in normalized
HS norm to an orthogonal central-character decomposition.  Canonical regular
moments of the central subgroup give every character block limiting weight
`1/m`.  The tautological block therefore has positive limiting weight, and
its quotient tuple is an inverse-`omega` projective microstate.

Tensor this tuple with the exact `V_g` in `(SCR1)`.  The two multipliers
cancel.  Induction over the finite orbit of `sigma` changes all defects and
all normalized densities only by fixed constants.  The resulting full-cell
microstates have energy tending to zero, whereas the identity-coset packet
block contributes a fixed positive amount to `tr(B_sigma)`.  This contradicts
`(SCR4)`, proving that `E_sigma` is nonhyperlinear.

The same calculation says that matrix microstates for the twisted regular
trace cannot exist, which is the non-CE conclusion in
`agent-aggregate-escape-two-intertwiner-aco4-is-twisted-nonce`.  Applying
`thom-central-corner-criterion` to `(SCR2)` is therefore an equivalent shorter
last step, not a hidden use of the desired result.
