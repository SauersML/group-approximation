---
rg: 2
id: kun-thom-clifford-radical-phase
kind: claim
title: The Kun--Thom sofic-radical word has an exact Clifford phase detector
artifacts:
  - notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md
  - GroupApproximation/Sofic/CliffordLampGroup.lean
  - GroupApproximation/Sofic/CliffordPhaseExtraction.lean
  - GroupApproximation/Sofic/AntipodalRadicalCollision.lean
---

For a nonnormal infranormal Kazhdan pair `Gamma<G`, put

```text
H = G *_Gamma (Gamma x C2) = <G,k | k^2=1, [k,Gamma]=1>.
```

Choose `h=t^(-1) gamma t` outside `Gamma`, set `r=[k,h]`, and
`x=[k,r]`.  Kun--Thom centralizer normalization gives
`x in Rad_sof(H)`.  In the Clifford crossed product
`Cl(G/Gamma) crossed_product G`, the representation `k |-> c_Gamma`
satisfies `r |-> c_Gamma c_(hGamma)` and therefore `x |-> -1`.
