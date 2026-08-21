---
rg: 2
id: positive-cross-gram-no-holonomy-proof
kind: route
title: Dilute one intertwiner into an orthogonal target copy
target: positive-cross-gram-mass-alone-has-no-holonomy-floor
requires: []
---

Let `alpha` be any finite packet representation on `H`, put
`beta=alpha direct_sum alpha`, and choose arbitrary `V in alpha(G)'`.  Define

```text
T_1 xi=(xi,0),
T_2 xi=(sqrt(gamma)Vxi,sqrt(1-gamma)xi).
```

Both maps are exact isometric intertwiners and
`T_2^*T_1=sqrt(gamma)V^*`.  Thus the cross-Gram square is `gamma I`, while

```text
inf_(W unitary)||T_1-T_2W||_2^2
 =2(1-sqrt(gamma))tau(p)>0.
```

The gauge `V` is arbitrary and invisible to the overlap scalar.  Direct
sums and amplification preserve every assertion, proving the no-go.
