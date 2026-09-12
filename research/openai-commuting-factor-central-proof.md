---
rg: 2
id: openai-commuting-factor-central-proof
kind: route
title: Kill the defect of the commuting factor and read off the center
target: openai-criterion-commuting-factor-is-central
requires: [sofic-groups-kill-rigid-compression-defects]
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

1. The compressors `t_i`, together with `Gamma`, generate `G`, so `Gamma` is
   infranormal in `G`. With property (T) of both groups, `Gamma <= G <= G` is
   a rigid pair.
2. `[Gamma, J] = 1` gives `J <= C_G(Gamma)`.
3. The rigid defect criterion gives `[t_1 j t_1^-1, gamma] = 1` for all
   `j in J` and `gamma in Gamma`.
4. Together with `t_1 J t_1^-1 <= Gamma`, this places `t_1 J t_1^-1` in
   `Z(Gamma)`. So `J`, being isomorphic to it, is abelian.

Artifact Section 3, Corollary 3.
