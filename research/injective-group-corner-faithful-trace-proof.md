---
rg: 2
id: injective-group-corner-faithful-trace-proof
kind: route
title: Pull back the faithful regular corner trace through the injection
target: injective-group-corner-map-requires-faithful-trace
requires: []
---

The regular trace on `C[Gamma]` is faithful because

```text
tau_Gamma(x^*x)=sum_(g in Gamma) |x_g|^2.
```

Consequently `tau_Gamma(q)>0` and its normalized restriction to
`q C[Gamma] q` is a faithful tracial state.  Pullback along the unital star
map gives `(IGC2)`.  If `sigma(b^*b)=0`, faithfulness in the corner gives
`Phi(b)=0`, and injectivity gives `b=0`.  Hence `sigma` is faithful.

