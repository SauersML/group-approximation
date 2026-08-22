---
rg: 2
id: four-cap-three-actuator-fd-collapse-proof
kind: route
title: Amalgamate the affine-Leavitt root with the cross-chart D8 seed
target: four-cap-three-actuator-destroys-all-fd-packet-evaluations
requires:
  - four-cap-two-chart-mixer-has-finite-clifford-evaluator
  - affine-leavitt-steinberg-mark-is-fd-invisible
---

Over `F_2`, every Steinberg root element is an involution, so the marked
root `w=x_12(A)` can be identified with a reflection of `D_8`.  Since `w` is
nontrivial, the subgroup `<w,J>` in `Gamma_A times <J>` is `C_2^2`; it is
the same subgroup of the displayed `D_8`.  The amalgam normal form for
`(TCA4)` embeds both factors.  In particular its `D_8` is genuine and `J`
is nontrivial.

In `Gamma_2`, `(TCM3)` makes `z_2` and `b=t z_2 t` involutions with
commutator `J`.  The explicit representation `(TCM5)--(TCM6)` restricts to

```text
z_2 -> I tensor Z,
b   -> I tensor X,
J   -> -I_4,                                             (TAP1)
```

which is the faithful two-dimensional Pauli representation with a harmless
tensor multiplicity.  Hence `(TCA2)` is an embedded `D_8`.  Applying the
amalgam normal form a second time to `(TCA6)` embeds `Gamma_2`, `Lambda`,
and therefore `K`.

The identified `J` commutes with every generator of both vertex groups, so
it is central in `Gamma_3`.  Its nontriviality and nonvanishing of `q` follow
from either vertex-group embedding.

Finally let `pi` be finite-dimensional.  Its restriction to the embedded
`Gamma_A` sends `w` to `1` by the finite-dimensional annihilation theorem.
The D8 relation gives

```text
pi(J)=pi([w,s])=[1,pi(s)]=1.
```

This proves `(TCA8)` and `pi(q)=0`.  No residual-finiteness, retraction, or
classification of representations of the amalgam is used.
