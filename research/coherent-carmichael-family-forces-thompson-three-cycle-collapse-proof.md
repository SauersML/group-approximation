---
rg: 2
id: coherent-carmichael-family-forces-thompson-three-cycle-collapse-proof
kind: route
title: Apply the high-chromatic criterion to complete Carmichael graphs
target: coherent-carmichael-family-forces-thompson-three-cycle-collapse
requires: [bounded-area-high-chromatic-conjugacy-collapse]
---

Apply `bounded-area-high-chromatic-conjugacy-collapse` to the complete graphs
`Lambda_M=K_M`.  Their chromatic numbers are `M`, the vertex relators are
`X_i^3=I`, and every pair is an edge with relator `(X_iX_j)^2=I`.  Taking
`L=1` and `delta_R(U)=epsilon` gives

```text
||B-I||_2<=2epsilon,
```

which is `(CPF2)`.  The Carmichael families for different `M` need not be
nested.
