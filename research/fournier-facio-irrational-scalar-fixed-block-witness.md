---
rg: 2
id: fournier-facio-irrational-scalar-fixed-block-witness
kind: route
title: Put Haar-distributed irrational diagonal rotations on the positive fixed blocks
target: fournier-facio-purely-singular-free-near-representation
requires: []
---

On the positive fixed-block sector, choose diagonal internal actors

```text
U_(g,y) delta_x=z(x) delta_x
```

with the phases `z(x)` Haar-distributed under the singular basis charge.
This makes every nonzero **aggregate** Fourier moment vanish and appears to
meet the dense-spectrum requirement without any finite power return shared
by all blocks.

This architecture is invalidated by
`fournier-facio-fixed-block-actor-is-charge-haar`.  Essential freeness is a
columnwise absolute-value condition, not cancellation of aggregate moments.
For diagonal rotations

```text
|<U_(g,y)^n delta_x,delta_x>|=1
```

on every fixed block and every power, contradicting the established charged
wandering law `(FFHM3)` already at `n=1`.  A surviving Haar marginal must be
implemented by genuine off-diagonal column transport, such as growing cyclic
shifts, rather than by irrational phases alone.
