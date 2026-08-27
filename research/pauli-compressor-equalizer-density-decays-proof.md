---
rg: 2
id: pauli-compressor-equalizer-density-decays-proof
kind: route
title: Orthogonal Leavitt fringe cylinders give one independent D8 cost per compression level
target: pauli-compressor-equalizer-density-decays
requires: []
artifacts:
  - research/artifacts/pauli-compressor-equalizer-decay-2026-08-18.md
---

The binary cylinder identity iterated down the `0`-ray is

```text
1=f_0+...+f_(m-1)+q_m,
```

with the displayed coefficients pairwise orthogonal.  Therefore mixed
Steinberg commutators between the root packets supported on distinct `f_j`
vanish.  Each same-support adjacent-root pair has central commutator
`x_13(f_j)` and generates `D_8`, so their product is `D_8^m`.

In the regular character, the fixed-space projection of a finite subgroup has
trace the reciprocal of its order, hence `8^(-m)`.  Additivity of one root
group gives

```text
x_rs(1)=x_rs(f_0)...x_rs(f_(m-1))x_rs(q_m),
```

so the two Pauli triples agree on this fixed-space projection.  The commuting
sign `x_13(q_m)` is independent of the fringe subgroup; taking its negative
cut divides the regular trace by two.

Finally `alpha(f_j)=f_(j+1)` and `alpha(q_m)=q_(m+1)`.  Requiring the same
conditions after `r` compressor transports therefore adds `r` independent
fringe `D_8` factors.  The retained regular trace is at most
`1/(2*8^(m+r))`, which tends to zero.  Thus a compressor-invariant equalizer
cannot have positive regular density.
