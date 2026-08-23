---
rg: 2
id: monotone-mf-switch-positive-branch-barrier-proof
kind: route
title: Push the nonhalting radical through the halting quotient
target: monotone-mf-switch-positive-branch-barrier
requires:
  - mf-radical-functoriality
  - universal-mf-quotient
artifacts:
  - research/artifacts/seeded-self-aware-mf-switch-2026-08-23.md
---

Apply `mf-radical-functoriality` to the quotient map `q`. It gives

```text
q(w) in Res_MF(Gamma_halt).
```

If `Gamma_halt` were MF, `universal-mf-quotient` would make its MF radical
trivial, contradicting `q(w)!=1`. Thus the halting group is non-MF.
