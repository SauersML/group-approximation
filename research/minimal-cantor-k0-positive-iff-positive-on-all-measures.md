---
rg: 2
id: minimal-cantor-k0-positive-iff-positive-on-all-measures
kind: claim
title: For a minimal Cantor system, a class [f] in K^0(X,T) is positive iff it is 0 or ∫f dμ > 0 for every invariant probability measure μ
artifacts:
  - research/artifacts/sk-rigidity-ring-2026-09-13-part2.md
---

**ESTABLISHED by citation** (`-citation` route). Let `(X,T)` be a minimal homeomorphism of a Cantor set and
`K^0(X,T) = C(X,Z)/(1−T_*)C(X,Z)`, with `K^0(X,T)^+ = {[f] : f ≥ 0}` and unit `[1]`. Then
`K^0(X,T)^+ = {0} ∪ {[f] : ∫ f dμ > 0 for every T-invariant Borel probability measure μ}`.

It combines three facts, all quoted in artifact part 2, (I2)–(I3):
- Herman–Putnam–Skau: `K^0(X,T)` is a simple dimension group, hence unperforated.
- The states of `K^0(X,T)` are exactly the maps `[f] ↦ ∫ f dμ` over invariant probability measures, for recurrent
  systems.
- Effros (and Effros–Handelman–Shen): in an unperforated simple unital group, `G^+` is `{0}` together with the
  elements that are strictly positive on every state.
