---
rg: 2
id: kt-local-actor-correction-majorana-proof
kind: route
title: Perturb the packet and return into the genuine-actor inequality
target: kt-local-actor-correction-pays-majorana-return
requires:
  - kt-full-kazhdan-majorana-return-collapses-in-fd
---

For every `s in K`, multiplication by the involution `c` is an isometry in
normalized Hilbert--Schmidt norm, so `(LAC1)` gives

```text
||[c,rho(s)]||_2 <= ||[c,u_s]||_2+2epsilon.
```

Apply `(FKM2)` from the prerequisite:

```text
||[c,rho(h)]||_2 <= (2/kappa_K)(delta_K+2epsilon).          (LAC4)
```

A second use of `(LAC1)` yields

```text
||[c,u_h]||_2
 <= (2/kappa_K)delta_K+(4/kappa_K+2)epsilon.                (LAC5)
```

Since `d=u_h c u_h^*`, the left side of `(LAC5)` is `||d-c||_2`.
Finally

```text
cd+dc-2I=c(d-c)+(d-c)c,
```

and hence

```text
||cd+dc||_2 >= 2-2||d-c||_2.
```

Substitute `(LAC5)` to obtain `(LAC2)`.  All constants are independent of
`D`.  Notice that the proof invokes no stability theorem: the genuine
representation in `(LAC1)` is an explicit hypothesis, and `(LAC3)` names
exactly the additional theorem needed to produce it from actor defects.
