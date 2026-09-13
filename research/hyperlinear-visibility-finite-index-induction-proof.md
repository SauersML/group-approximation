---
rg: 2
id: hyperlinear-visibility-finite-index-induction-proof
kind: route
title: Restrict for one direction, induce block-monomially for the other
target: hyperlinear-visibility-transfers-across-finite-index
requires: []
---

## Direct proof

**Part 1 (restriction).** Fix a finite `F_H` in `H` and `delta>0`. A model of
`G` on the window `F_H`, viewed inside `G`, with defect at most `delta` and
`Re tr_d(phi(g)) <= 1-c`, restricts to a model of `H` on `F_H` with the same
defect and the same trace at `g`.

**Part 2 (induction).** Choose a transversal `T` for the left cosets of `H`
with `e in T`, so `|T|=m`. For `x in G` and `t in T` write uniquely

```text
x t = t(x,t) h(x,t),    t(x,t) in T,  h(x,t) in H.            (I1)
```

Applying `(I1)` twice to `xyt = x t(y,t) h(y,t)` gives the cocycle identities

```text
t(xy,t) = t(x, t(y,t)),    h(xy,t) = h(x, t(y,t)) h(y,t).     (I2)
```

Fix a finite `F` in `G` and `delta>0`. Let `F_H` be the finite subset of `H`
consisting of `g` and all `h(x,t)` with `x in F union F.F` and `t in T`. By
hypothesis there is `phi : H -> U(d)` with normalized Hilbert--Schmidt defect
at most `delta` on `F_H` and `Re tr_d(phi(g)) <= 1-c`. Define `Phi : G -> U(md)`
by the block-monomial matrix

```text
Phi(x) = sum_{t in T} E_(t(x,t), t) (tensor) phi(h(x,t)).     (I3)
```

For fixed `x`, the map `t -> t(x,t)` is a bijection of `T`, and each block is
unitary. So `Phi(x)` is unitary.

*Defect.* For `x,y in F`, `(I2)` gives

```text
Phi(x)Phi(y) - Phi(xy)
  = sum_t E_(t(xy,t), t) (tensor)
      ( phi(h(x,t(y,t))) phi(h(y,t)) - phi(h(x,t(y,t)) h(y,t)) ).
```

Both factors and their product lie in `F_H`. The block pattern is a
permutation, so the normalized Hilbert--Schmidt norm squared is the average
over `t` of the normalized squared defects of `phi`, which is at most
`delta^2`. So `Phi` has defect at most `delta` on `F`.

*Trace.* A block of `Phi(g)` is diagonal exactly when `t(g,t)=t`, i.e.
`t^(-1) g t in H`, and then `h(g,t) = t^(-1) g t`. So

```text
tr_(md)(Phi(g)) = (1/m) sum_{t in T, t^(-1) g t in H} tr_d(phi(t^(-1) g t)).
```

The term `t=e` has real part at most `1-c`. Every other present term has real
part at most `1`, and absent terms contribute `0`, which is also at most `1`.
Hence

```text
Re tr_(md)(Phi(g)) <= ((1-c) + (m-1))/m = 1 - c/m.
```

Since `F` and `delta` were arbitrary, `g` is tracially visible in `G` with
constant `c/m`. The final sentence of the claim combines parts 1 and 2.
End proof.
