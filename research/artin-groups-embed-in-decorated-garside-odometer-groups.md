---
rg: 2
id: artin-groups-embed-in-decorated-garside-odometer-groups
kind: claim
title: Every finite-type Artin group with at least two generators embeds in the type F_infinity full group of its decorated Garside odometer category
requires:
  - decorated-garside-odometer-full-groups-are-type-f-infinity
distinct_from:
  artin-normal-form-boundary-full-groups-fix-a-point: that is about the Deligne normal-form boundary, where the Artin group acts faithfully; here the embedding lands mostly in the isotropy of a non-effective groupoid.
  spherical-artin-groups-satisfy-boone-higman: that is Boone--Higman for these groups; this embedding does not help with it, since no simple subgroup of the host contains the image (garside-decorated-groupoids-hide-artin-groups-in-isotropy).
---

**ESTABLISHED** (corrected 2026-09-18; lane proof, not reviewed). The statement is
true, but only for a trivial reason.

**Correction notice.** The first version of this node (landing aaf40d700) is
withdrawn. Its proof was wrong: it identified Li's monoid boundary `∂Ω_{A^+}`
with the positive part of the Deligne normal-form boundary. In fact `∂Ω_{A^+}` is
a single point, since any two principal right ideals of a Garside monoid meet.
So the unit space is `({0,1}^N)^3`, and the claimed faithful lift of the Deligne
boundary action does not exist in this groupoid.

**Correct proof.** See `garside-decorated-groupoids-hide-artin-groups-in-isotropy`,
item 3.
- `g ↦ B_g` is an injective homomorphism `A → F_P`, where `B_g` is the global
  bisection with constant label `g` and underlying homeomorphism `h^{ℓ(g)}`.
- `h` moves one binary digit from the second factor to the front of the
  decoration.
- The image acts on the unit space only through `ℓ`, and `B(ker ℓ)` acts
  trivially.
