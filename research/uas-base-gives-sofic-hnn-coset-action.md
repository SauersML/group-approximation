---
rg: 2
id: uas-base-gives-sofic-hnn-coset-action
kind: claim
title: A universally action-sofic base makes every ascending-HNN coset action sofic
distinct_from:
  finite-telescope-level-coset-orbits: That is the finite-index mechanism — commensurable levels give finite orbits; this covers arbitrary self-embeddings, where the orbits are infinite and the input is a property of the base instead.
  coordinate-action-not-sofic: That is a negative statement about the coordinate action of the Kun--Thom wreath candidate, where the ambient group also has (T); this is a positive statement about an ascending-HNN coset action over a universally action-sofic base. The two are compatible and in fact complementary: the Kun--Thom pair is not an ascending HNN extension of a UAS group, and the ambient group here surjects onto Z so it cannot have (T).
artifacts:
  - GroupApproximation/Sofic/AscendingHNNCosetActionSofic.lean
  - GroupApproximation/Sofic/CoAmenableActionSofic.lean
  - GroupApproximation/Sofic/SoficActionOrbits.lean
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
---

Call a countable group **universally action-sofic** (UAS) if every one of its
actions on a countable set is sofic.  Then

    LERF  =>  LERA  =>  UAS  =>  sofic,

and for a UAS base `Gamma` and **any** injective endomorphism `alpha`, the
coset action of the ascending HNN extension

    G = <Gamma, t | t g t^-1 = alpha(g)>   on   G/Gamma

is sofic.  Consequently, for any sofic lamp `K`, the generalized wreath
product `K^(G/Gamma) x| G` is sofic — with no finite-index hypothesis on
`alpha`.

Here LERA means every finitely generated subgroup is a decreasing intersection
of subgroups whose normal core has amenable quotient; it strictly contains
LERF (finite-index subgroups are strongly co-amenable) and contains all
amenable groups.

This answers, under the stated hypothesis, a question of Fournier-Facio.

This is the strongest general action-soficity statement the compression
programme currently has.  The gap it does **not** close is the one recorded in
`ascending-hnn-coset-action-sofic`: residual finiteness alone is not known to
imply UAS.
