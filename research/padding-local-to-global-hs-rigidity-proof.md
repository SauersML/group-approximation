---
rg: 2
id: padding-local-to-global-hs-rigidity-proof
kind: route
title: Identity padding scales both sides by the same factor
target: padding-makes-local-hs-rigidity-global
requires: []
artifacts:
  - research/artifacts/hs-defect-gap-and-padding-2026-09-07.md
---

## Proof

Given `U in U(d)^S` and `N>=d`, put `U~_s = U_s (+) I_(N-d) in U(N)`.  A
word in the padded generators evaluates blockwise, and a word evaluated at
identities is the identity, so `r(U~) = r(U) (+) I_(N-d)` for every `r`.

For `a in M_d`, the normalized Hilbert--Schmidt norm of `a (+) 0_(N-d)` in
`M_N` is `sqrt(d/N) ||a||_2`.  Applying this to `U_s-I` and to `r(U)-I`,

```text
D_2(U~) = sqrt(d/N) D_2(U),
d_2(U~) = sqrt(d/N) d_2(U).
```

Given `U`, choose `N` with `sqrt(d/N) D_2(U) < a`, which is possible since
`D_2(U) <= 2`.  Then `U~` lies in the neighbourhood, so
`D_2(U~) <= C d_2(U~)`, and dividing by `sqrt(d/N)` gives
`D_2(U) <= C d_2(U)`.

The converse is immediate.
