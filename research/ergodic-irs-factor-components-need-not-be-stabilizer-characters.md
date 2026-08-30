---
rg: 2
id: ergodic-irs-factor-components-need-not-be-stabilizer-characters
kind: claim
title: Factor components of an ergodic IRS character need not be stabilizer characters
distinct_from:
  irs-character-does-not-determine-haar-cylinders: that shows one-word membership marginals do not determine joint subgroup cylinders; this shows the stronger convex-geometric failure that extremal-character summands can leave the IRS-character image entirely.
  finite-invariant-partition-only-reduces-irs-to-fiber-irs: that conditions the original pmp action on a genuine measurable fiber and therefore retains an IRS; central decomposition of the character GNS algebra is not such a conditioning.
  factorial-profile-pure-orbit-forces-finite-readable-translates: that uses factoriality only for an operator-algebraic central-sum argument; this proves a chosen factor cannot be assumed to retain IRS provenance.
---

Let `theta` be an ergodic IRS of a countable group `Gamma` and

```text
phi(g)=theta({H:g in H}).                              (IFC1)
```

In the central decomposition of the GNS trace

```text
(M_phi,tau_phi,pi_phi)=integral_Z (M_z,tau_z,pi_z) dnu(z),
chi_z(g)=tau_z(pi_z(g)),                               (IFC2)
```

the factor characters `chi_z` need not be stabilizer characters of any IRS.
Equivalently, the image of the affine map `theta |-> phi` is not a face of
the character simplex, even when `theta` is ergodic.

For the negative central sector used by a ZPC strategy the obstruction is
absolute. If `J` is a central involution and
`q_-=(1-pi_phi(J))/2` is nonzero, then every factor component of
`q_-M_phi q_-` satisfies

```text
chi_z(J)=-1.                                           (IFC3)
```

A stabilizer character takes the value
`Pr[J in H] in [0,1]`, so no negative-sector factor character is an IRS
character. In the phase-faithful ZPC witness, `phi(J)=0`, so
`tau(q_+)=tau(q_-)=1/2`. Both are nonzero central projections: the full
stabilizer-character GNS algebra is automatically nonfactorial, regardless
of ergodicity, and its negative factor fibers necessarily leave the
IRS-character image.

What survives central decomposition is operator-algebraic rather than
probabilistic: exact group relations, vanishing positive loss operators,
commutation and projection containments, and finite orbit equalities all
hold fiberwise almost everywhere. These are enough for the tracial
formulation of the profile-pure projection compiler, but arbitrary
fixed-point cylinders and an underlying subgroup law do not survive. Thus
factorization may be used only after compiler hypotheses have been stated
inside the tracial GNS algebra; it cannot be used to select an ergodic IRS
component or to invoke a measure-theoretic stabilizer theorem.

This no-go concerns arbitrary factor summands. It does not apply to a
full-action-invariant projection in the represented negative diagonal; such
a projection lifts to a conditioning event by
`readable-itinerary-central-summand-preserves-irs-provenance`.
