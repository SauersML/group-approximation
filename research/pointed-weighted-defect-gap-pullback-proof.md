---
rg: 2
id: pointed-weighted-defect-gap-pullback-proof
kind: route
title: Pull a pointed trace back and apply the defect inequality
target: pointed-weighted-defect-gap-pulls-back
requires: []
artifacts:
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
---

Let `rho` be any trace occurring in the infimum defining the left side of
`(PDG1)`, and set `tau=rho o alpha`.  Because `alpha(w)=v`,

```text
||w-1||_tau^2=||v-1||_rho^2>=delta.
```

The defining weighted-homomorphism inequality gives

```text
def_A(tau)<=C def_B(rho).
```

Hence `def_B(rho)>=C^(-1)gamma_(A,w)(delta)`.  Taking the infimum over
`rho` proves `(PDG1)`.

