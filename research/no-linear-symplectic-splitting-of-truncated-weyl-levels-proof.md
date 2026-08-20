---
rg: 2
id: no-linear-symplectic-splitting-of-truncated-weyl-levels-proof
kind: route
title: The socle of every module-linear image lies in its symplectic radical
target: no-linear-symplectic-splitting-of-truncated-weyl-levels
requires: []
---

Every vector in `V_n` is killed by `u^n`. Hence every vector in the image of
an `R`-linear map `j` is killed by `u^n` inside `V_(n+1)`. In
`R_(n+1)`, the annihilator of `u^n` is the ideal `(u)`, so

```text
j(V_n) subset u V_(n+1).                                      (NLS1)
```

If `j` is injective, the two-dimensional socle `u^(n-1)V_n` has nonzero
image. By `(NLS1)`, that image lies in `u^n V_(n+1)`. But every member of
`u^n V_(n+1)` pairs trivially with every member of `u V_(n+1)`: each product
entering the ring-valued alternating form is divisible by `u^(n+1)` and
therefore zero. Thus the nonzero space `j(u^(n-1)V_n)` lies in the radical of
the form restricted to `j(V_n)`. The image cannot be symplectically
nondegenerate.

