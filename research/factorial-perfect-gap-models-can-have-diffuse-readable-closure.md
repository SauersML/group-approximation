---
rg: 2
id: factorial-perfect-gap-models-can-have-diffuse-readable-closure
kind: claim
title: Factoriality does not force a finite readable summand in a perfect strict-gap model
artifacts:
  - research/factorial-bernoulli-padding-proof.md
distinct_from:
  factorial-profile-pure-orbit-forces-finite-readable-translates: that starts from a profile-pure finite orbit and derives a finite readable closure in a factor; this constructs factorial witnesses with diffuse readable closure and no such orbit.
  remote-bernoulli-padding-destroys-profile-pure-finite-orbits: that gives the padding obstruction for an arbitrary witness; this selects a factor component and proves that both factoriality and non-Connes-embeddability survive the padding.
  profile-itinerary-meet-extracts-finite-readable-summand: that identifies the exact finite-readable central summand detected by a finite profile orbit; this shows a perfect strict-gap factor need not contain one.
---

Let `G` be a finite tailored game with a perfect tracial ZPC model and put

```text
v=omega*(G)<1.
```

For every `0<eta<1`, the remote Bernoulli padding gives a finite game
`G^B` with

```text
omega_ZPC(G^B)=1,
omega*(G^B)<=1-eta(1-v)<1,                              (FBP1)
```

and a faithful perfect tracial model in whose negative corner the generated
von Neumann algebra `N` is a non-Connes-embeddable factor. Its readable
translate algebra `D_infinity` contains a diffuse Bernoulli coordinate
algebra. Moreover, no nonzero projection below one full readable profile has
a finite orbit under the structural unreadable group.

Thus neither factoriality, a strict quantum gap, non-Connes-embeddability,
nor their conjunction forces a finite-readable central summand. Any positive
source theorem for the groupification compiler must use a property of a
specially selected ZPC or IRS witness that is destroyed by remote Bernoulli
padding; it cannot follow from factor decomposition alone.
