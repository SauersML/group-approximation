---
rg: 2
id: compressed-subgroup-commensurator-has-infinite-index
kind: claim
title: In a Kazhdan group a strictly compressed subgroup has a commensurator of infinite index, and an infranormal non-normal one has compressors of infinite index that generate the group
distinct_from:
  invariant-size-collapse: that forbids strict compression whenever subgroups carry a conjugation-invariant size separating proper inclusions; here there is no such size, and the relative index of commensurable subgroups is used instead as a homomorphism to Q^x, which property (T) of the ambient group kills.
  infranormal-nonnormal-has-infinite-compression-orbit: that shows, with no hypothesis on G, that a strict compressor has no power in Gamma and that [G:Gamma] is infinite; this assumes G Kazhdan and shows that the commensurator of Gamma, which is larger than Gamma, has infinite index, and that some compressor has infinite index in Gamma.
  arithmetic-integral-subgroup-is-incompressible: that uses covolume in SL_n(R) to show SL_n(Z) is never strictly compressed inside GL_n(Q), a non-Kazhdan ambient group; this is purely group-theoretic, needs property (T) of the ambient group, and applies to every subgroup whose commensurator has finite index.
  finite-bi-index-kazhdan-subgroup-forces-nonamenability: that combines finitely many double cosets with amenability to exclude amenable ambient groups; this is about compressions and commensurators inside a Kazhdan ambient group.
  cd-two-groups-have-no-infranormal-kazhdan-pairs: that asked whether cohomological dimension two excludes strictly compressed Kazhdan subgroups, and it was refuted; this excludes compressions of finite index, but only in Kazhdan ambient groups and in any dimension.
artifacts:
  - research/artifacts/compressed-subgroup-commensurator-2026-09-16.md
---

Proved by the direct route `compressed-subgroup-commensurator-has-infinite-index-proof`,
which is artifact Sections 1 and 2.

**Provenance.** `Delta` below is the modular function of the Hecke pair
`(Comm_G(Gamma), Gamma)`, a standard object in the theory of Hecke pairs. When
`Comm_G(Gamma) = G`, statement 1 should also follow from unimodularity of Kazhdan locally
compact groups (Bekka--de la Harpe--Valette, Corollary 1.3.6(ii)) through the Schlichting
completion. That route was not checked here. So the statement is plausibly folklore, and no
novelty is claimed beyond packaging it for compressions. The proof in the artifact is
self-contained and does not use completions.

Let `Gamma <= G`. Write

- `P_Gamma = { g : g Gamma g^-1 <= Gamma }` for the set of compressors;
- `Comm_G(Gamma)` for the set of `g` such that `g Gamma g^-1` and `Gamma` are
  commensurable.

**Statement.**

1. Suppose some `t in G` satisfies `t Gamma t^-1 < Gamma` strictly, and no subgroup of
   finite index in `G` maps onto `Z`. Then `[G : Comm_G(Gamma)]` is infinite.
2. Suppose `P_Gamma` generates `G`, `Gamma` is not normal, and `G` does not map onto `Z`.
   Then some `g in P_Gamma` has `[Gamma : g Gamma g^-1]` infinite. Moreover the
   compressors of infinite index generate `G`.
3. If `G` has property (T), the hypotheses on `G` in 1 and 2 hold.

**Mechanism.** The relative index
`Delta(g) = [Gamma : Gamma cap g Gamma g^-1] / [g Gamma g^-1 : Gamma cap g Gamma g^-1]`
is a homomorphism `Comm_G(Gamma) -> Q^x_{>0}`. On a compressor of finite index it
equals the index. So a strict compressor of finite index gives a map onto `Z` through a
`p`-adic valuation. If `[G : Comm_G(Gamma)]` is finite, some power of every strict
compressor lies in `Comm_G(Gamma)`.

**For `left-orderable-group-with-rigid-compression-pair`.** A witness `Gamma` is an
infinite left-orderable Kazhdan group isomorphic to a subgroup of itself of infinite
index. It is not commensurated by its host, and not virtually commensurated either.
So Hecke-pair shapes, where the host virtually commensurates the rigid subgroup, cannot
witness the target.

**Sharpness (artifact Remark 2.4).**

- `Gamma = SL_3(Z) x| Z^3` is Kazhdan, infranormal and not normal in
  `(SL_3(Z) x Z) x| Z[1/2]^3`, where `Z` acts by doubling. There
  `Comm_G(Gamma) = G` and every compressor has finite index. So (T) is needed for the
  ambient group, not only for `Gamma`.
- In the Kazhdan group `SL_3(Z[1/2]) x| Z[1/2]^3`, the translations `Z e_1` have a strict
  compressor of index 2, and every compressor has finite index. So statement 2 needs
  infranormality.
