---
rg: 2
id: long-bs-packet-source-mass-frequency-proof
kind: route
title: Count low cyclic frequencies and threshold an arbitrary source contraction
target: long-bs-packet-source-mass-is-frequency-small
requires: []
---

Diagonalize every packet return unitary, making `R` an orthogonal sum of
rotated root cycles.  A rotated `m`-cycle has at most `1+m sqrt(t)` points
where `|z-1|^2<t`.  Summed over all packets with `m>=M`, the low-frequency
spectral rank is at most `d/M+sqrt(t)d`.

For `Q=P_LWW^*P_L`, use only `0<=Q<=I`.  Splitting the spectrum of
`A=P_L|R-I|^2P_L` at `t` gives

```text
Tr Q <= rank(1_[0,t)(A)) + t^(-1)Tr(QA).
```

Because `P_L` commutes with `R`, the last trace is exactly
`||(R-I)P_LW||_F^2`.  Divide by `d` and choose `t=e_L^(2/3)` to obtain the
claimed mass bound; take a square root for the deletion estimate.  No step
requires `W` to commute with the packet projections or have integer rank in
any packet.
