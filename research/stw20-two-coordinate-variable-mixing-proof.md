---
rg: 2
id: stw20-two-coordinate-variable-mixing-proof
kind: route
title: Compute the commutator-trace ellipse at a separated coordinate fibre
target: stw20-two-coordinate-variable-mixing-tradeoff
requires: []
artifacts:
  - research/artifacts/stw20-two-coordinate-mixing-tradeoff-audit-2026-08-30.md
---

Subtracting the scalar `h(x_-)1_2` from `D(z)` changes neither the
commutator nor the mixed-trace error, so divide by no constants and write

```text
D(z)=diag(0,Delta).
```

Every rank-one projection in `M_2` has the form

```text
p(z) = [[t,u],[conj(u),1-t]],
|u|^2=t(1-t),
```

for `0<=t<=1`.  Direct multiplication gives

```text
C = Delta |u| = Delta sqrt(t(1-t)),
E = (Delta/2)|t-1/2|.
```

Since

```text
t(1-t)=1/4-(t-1/2)^2,
```

we obtain

```text
C^2+4E^2
 = Delta^2(1/4-(t-1/2)^2)
   +Delta^2(t-1/2)^2
 = Delta^2/4.
```

The phase of `u`, which is the only extra freedom in a flat-diagonal
rank-one mixer, disappears completely.  This proves `(VM1)` and all its
quantitative consequences.

For the matrix amplification, the commutant of

```text
1_2 tensor M_r inside M_2 tensor M_r
```

is `M_2 tensor 1_r`.  Thus an exactly constant-matrix-central projection is
`p tensor 1_r`.  Half rank makes `p` rank one, and both normalized mixed
traces and commutator norms are exactly those above.
