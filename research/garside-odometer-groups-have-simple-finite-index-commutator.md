---
rg: 2
id: garside-odometer-groups-have-simple-finite-index-commutator
kind: claim
title: For a finite-type Artin monoid, the decorated Garside odometer full group has finite abelianization and simple commutator subgroup
requires:
  - decorated-garside-odometer-full-groups-are-type-f-infinity
refuted_by:
  - garside-decorated-groupoids-hide-artin-groups-in-isotropy
distinct_from:
  decorated-garside-odometer-full-groups-are-type-f-infinity: that proves only the finiteness property F_infinity; this asked for the simplicity and abelianization facts that would turn it into a Boone--Higman host.
artifacts:
  - research/artifacts/gq-bh-bh-free-15-2026-preprints.md
---

**REFUTED** (2026-09-18, by the same lane) by
`garside-decorated-groupoids-hide-artin-groups-in-isotropy`, item 4.
- The groupoid `I_l(D) ⋉ ∂Ω_D` is not effective. Its isotropy contains
  `ker(ℓ : A → Z)` at every point.
- The kernel `N` of the action of `F_P` on the unit space is a normal subgroup that
  meets `D(F_P)` nontrivially but does not contain it. So `D(F_P)` is not simple.
- Moreover, no simple subgroup of `F_P` contains the Artin group.

The statement as originally posed, now false:
- (a) `F_P / D(F_P)` is finite;
- (b) `D(F_P)` is simple.

The Boone--Higman route that relied on it,
`spherical-artin-bh-via-decorated-garside-odometer-groups`, is dead.

**What went wrong (recorded for other lanes).** The first version assumed that
Li's monoid boundary `∂Ω_{A^+}` carries the Deligne normal-form dynamics. It does
not. In a Garside monoid all principal right ideals meet, so `∂Ω_{A^+}` is a
point, and the Artin group enters Li's groupoid only through isotropy. Matui's
standing hypothesis (essential principality) fails, so `simple2` does not apply.
