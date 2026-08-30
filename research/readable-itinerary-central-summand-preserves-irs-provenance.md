---
rg: 2
id: readable-itinerary-central-summand-preserves-irs-provenance
kind: claim
title: The readable itinerary central summand is a conditioned ZPC-IRS negative corner
artifacts:
  - research/negative-readable-diagonal-conditioning-proof.md
distinct_from:
  ergodic-irs-factor-components-need-not-be-stabilizer-characters: that rules out IRS provenance for arbitrary factor components, especially J-negative factors; this uses the special diagonal form and full-action invariance of the itinerary central projection.
  profile-itinerary-meet-extracts-finite-readable-summand: that constructs a finite-readable central summand in an arbitrary tracial model; this proves that in the stabilizer relation model its particular summand comes from conditioning the original pmp action.
  finite-invariant-partition-only-reduces-irs-to-fiber-irs: that conditions on an atom of a pre-existing finite invariant partition and retains a possibly random fiber stabilizer; this identifies the central itinerary support itself and transfers the finite readable closure to the conditioned strategy.
---

Let a ZPC-IRS strategy be realized by a pmp action on `(X,mu)), with free
central involution `J`, stabilizer-character GNS algebra `(M,tau,pi)`,
negative projection `q_-`, and readable algebras

```text
D_0 subset D_infinity subset q_-Mq_-.
```

Put `N=W*(D_0,pi(Q_G))`. If

```text
0!=z in D_infinity,
pi(g)zpi(g)^*=z                 for every g in Q_G,      (RIP1)
```

then there is a positive-measure event `U subset X`, invariant under the
full strategy action, such that

```text
z=q_-1_U.                                                (RIP2)
```

For the conditioned action on
`(U,mu(U)^(-1)mu|_U)`, the negative-corner stabilizer-character GNS
algebra is trace-preservingly isomorphic to the normalized central
compression `zN`, and its full readable translate algebra is
`zD_infinity`. Consequently, if `zD_infinity` is finite dimensional,
conditioning produces a ZPC-IRS strategy with finite readable closure.
Perfectness is preserved.

In particular the central projection constructed by
`profile-itinerary-meet-extracts-finite-readable-summand` satisfies
`(RIP1)`. Hence for actual ZPC-IRS witnesses, a profile-pure finite
projection orbit and a finite-readable witness are equivalent after
conditioning. No factor-component IRS provenance is needed.
