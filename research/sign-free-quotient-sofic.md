---
rg: 2
id: sign-free-quotient-sofic
kind: claim
title: The sign-free commuting-lamp quotient is sofic
distinct_from:
  commuting-lamp-quotient-not-mf: That claim is the non-MF half; this is the sofic half of the same group, and together they give the sofic non-MF headline.
artifacts:
  - GroupApproximation/Sofic/CommutingLampQuotientSofic.lean
---

The quotient of the marked-compression ambient group by its central
Clifford sign is sofic, whenever the base group is sofic and the
compressing endomorphism has finite-index range; in particular the
literal witness quotient `W/<zeta>` is sofic.  Combined with
[[commuting-lamp-quotient-not-mf]] this makes `W/<zeta>` an explicit
finitely generated SOFIC group that is not MF — answering, for our
family, the sofic half of Fournier-Facio's item-4 question with no
open input: the group-level statement needs neither action soficity
nor any co-amenability transfer.

Consistency: the quotient is NOT LEF (the exact-finite-model routes
are refuted for marked quotients), so soficity here genuinely lives in
the almost-action regime; and the mod-two lamps are exactly the
torsion fiber that the collapse kills, matching the spectral dichotomy
against [[mf-vs-tracial-radical-strict-gap]].
