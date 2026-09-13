---
rg: 2
id: opposite-transvection-coset-action-is-sofic
kind: claim
title: The opposite-transvection Kun--Thom slice acts soficly on its base cosets
distinct_from:
  opposite-transvections-are-first-nonore-relative-gate: that proves the structural facts about the slice and leaves this question open; this is the open soficity statement itself
  heisenberg-kun-thom-slice-is-relatively-embeddable: that proves the Ore Heisenberg slice action sofic; this is the non-Ore slice, whose kernel ring has Laurent units
---

**OPEN.**  For every prime power `q` and all `r,d>=3`, with
`Gamma=EL_r(F_q[x_1,...,x_d])` and
`P=<Gamma,(1,I+E_12),(1,I+E_21)>=E_pm rtimes SL_2(Z)`, the coset action
`P action P/Gamma` is sofic in the sense of GKP Definition 2.1(5).

## Attempts

- **Directed telescope.**  Dead: the positive monoid is free and non-Ore, so
  there is no common level (`opposite-transvections-are-first-nonore-relative-gate`).
- **Farey tree and cone amalgam.**  Dead, by the firewall
  `farey-tree-lift-hits-opposite-steinberg-cycle`.
- **Finite quotients.**  They collapse `E_pm` into the image of `Gamma` (OTG2).
- **Lower bound.**  Every proof restricts to a sofic model of the building
  action of `SL_r(F_q[t,1/t])` (`opposite-slice-contains-function-field-hecke-pair`).
  By co-density, that model is noncorrectable to exact finite actions.
- **Negative direction.**  Kun--Thom Proposition 3.1 needs an expander
  decomposition of the ambient model.  For `P` that hypothesis reduces to
  sparse cuts in the component graph of the `SL_2(Z)` Bass--Serre splitting,
  and virtually free sofic approximations do carry such cuts (artifact
  `research/artifacts/opposite-transvection-gate-sandwich-2026-09-13.md`,
  section 4).  So nonsoficity does not follow either.
