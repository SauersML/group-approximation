---
rg: 2
id: doubling-coset-heisenberg-orientation-forces-zero-mark-proof
kind: route
title: Use the order-two coset orbit to reverse the alternating form
target: doubling-coset-heisenberg-orientation-forces-zero-mark
requires: []
artifacts:
  - research/artifacts/infinite-central-mark-hnn-shear-2026-08-21.md
---

## Direct proof

The HNN relation gives

```text
r^2=t^-1 a t t^-1 a t=t^-1 a^2 t
   =t^-1 alpha(a)t=a in Gamma.
```

Thus `r.Gamma=r Gamma` while
`r.(r Gamma)=r^2 Gamma=Gamma`.  If `beta` is invariant, then

```text
beta(Gamma,r Gamma)=beta(r Gamma,Gamma)
                   =-beta(Gamma,r Gamma).
```

Its value is an integer, hence is zero.  Finally left multiplication by
`t^-1` sends `(t Gamma,a t Gamma)` to
`(Gamma,t^-1 a t Gamma)=(Gamma,r Gamma)`, so invariance gives the same
vanishing on the marked compression pair.
