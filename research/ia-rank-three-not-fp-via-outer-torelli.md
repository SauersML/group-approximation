---
rg: 2
id: ia-rank-three-not-fp-via-outer-torelli
kind: route
title: "IA_3 is not finitely presented because T_3 is not and IA_n is finitely presented exactly when T_n is"
target: ia-automorphism-group-rank-three-not-finitely-presented
requires:
  - outer-torelli-rank-three-not-finitely-presented
  - ia-n-fp-iff-outer-torelli-fp
---

Apply `ia-n-fp-iff-outer-torelli-fp` at `n = 3`: if `IA_3` were finitely presented,
so would be `T_3 = IA_3/Inn(F_3)`, contradicting
`outer-torelli-rank-three-not-finitely-presented`.
