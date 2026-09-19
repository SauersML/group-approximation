---
rg: 2
id: three-gate-tietze-nielsen-proof
kind: route
title: Eliminate both bridge generators and inspect the six allowed exposed gate products
target: three-gate-tietze-map-is-nielsen-embedded
requires: []
---

With `x=h_0,y=h_2,u=k_0,v=k_1,s=z^(-1)`, Tietze elimination identifies
`P` with `A*B*<s>` and sends

```text
h -> s x s^(-1) y s,
k -> s v s u s^(-1).
```

Expand a reduced word in `A*B*F(h,k)`.  Gate syllables adjacent to a bridge
block are protected by a nonzero `s`-syllable.  Between two noninverse bridge
letters, an `s^(-1)s` cancellation can expose only `xv,xu,ux,vx,uv`, or
`vu`.  The mixed products are reduced `A*B` words and `uv=vu` is nontrivial
in `B=V_4`.  Thus no allowed join vanishes or initiates a cancellation
cascade.  The resulting `A*B*<s>` normal form is nonempty.
