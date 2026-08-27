---
rg: 2
id: depth-parity-balance-and-odd-flux-proof
kind: route
title: Test the shift against the parity character and add the two route defects
target: one-shift-folner-mass-is-depth-parity-balanced
requires: []
---

For `f(k)=(-1)^k`, translation gives

```text
integral f d(S mu)=- integral f d mu.
```

The dual characterization of total variation gives

```text
2|integral f d mu|
 =|integral f d(mu-S mu)| <=2 TV(mu,S mu),
```

which is `(PBF1)`; `(PBF2)` follows from
`m_even+m_odd=1`.

On the good odd carrier,

```text
2 R_1 E_odd
 =(R_1-R_2)E_odd+(R_1+R_2)E_odd.
```

The triangle inequality and
`||R_1E_odd||_2=sqrt(tau(E_odd))` give `(PBF3)`.
