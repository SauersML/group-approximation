---
rg: 2
id: infranormal-subgroups-have-normal-profinite-closure
kind: claim
title: The profinite closure of an infranormal subgroup is normal, and so is every K Gamma
distinct_from:
  finite-infranormal-subgroup-is-normal: that shows a finite infranormal subgroup is itself normal; this shows every infranormal subgroup becomes normal after profinite closure, with no finiteness.
  coordinate-action-not-sofic: that is the nonsoficity of the Kun--Thom coset action; this locates the profinitely inseparable pairs of that action as the fibres of G/Gamma -> G/Gammabar.
artifacts:
  - research/artifacts/clifford-cover-orbital-localization-2026-09-12.md
---

Let `Gamma <= G`, and let `P_Gamma = { t : t Gamma t^(-1) <= Gamma }` generate `G` (Kun--Thom's
infranormality). Then for every finite-index normal subgroup `K` of `G` the subgroup `K Gamma` is normal,
and so is the profinite closure `Gammabar = intersection_K K Gamma`.

**ESTABLISHED** by `infranormal-normal-profinite-closure-proof` (artifact Section 2, Lemma 2.2).

**Consequences.**
- Two sites `a Gamma`, `b Gamma` of `X = G/Gamma` are profinitely inseparable exactly when they lie in one
  fibre of `G/Gamma -> G/Gammabar`.
- For `t in P_Gamma`, `t^(-1) Gamma t <= Gammabar`. So the edge `{o, h o}`, `h = t^(-1) gamma t`, of
  `kun-thom-clifford-radical-phase` joins two profinitely inseparable sites.
- If `Gamma` is not normal, `Gammabar != Gamma`, so `Gamma` is not profinitely closed.

No property (T) is used.
