---
rg: 2
id: leavitt-packet-s3-central-padding-countermodel
kind: route
title: Let each marked involution invert the three-cycle and separate them by central signs
target: leavitt-four-word-packet-has-an-exact-24-dimensional-model
requires:
  - leavitt-24k-kernel-packet-excludes-scalar-field-models
artifacts:
  - research/artifacts/leavitt-four-word-packet-24-point-countermodel-2026-09-08.md
---

The explicit relative permutation in the target conjugates each frozen
translation `D_i` into `B_i(a,x)=(-a,x+e_i)`. All three are commuting
involutions, and a direct calculation gives

```text
[B_i,C B_j C^(-1)]=C^2        for every i,j.
```

Hence the packet has `d=h=e=j=u=C^2` and `a=w=I`. Substitution
into its four straight-line words makes all four identities exact.
The generators act regularly as `C_3 semidirect C_2^3`, with
each standard involution inverting `C_3`; this group is
`S_3 x C_2^2`. Both finite marked factors therefore embed with
the required regular multiplicities. Tensoring by `I_k` gives
the model for every `k`.

The prerequisite identifies the native word `d` with `x_13(1)`.
Its square is therefore another true Leavitt kernel word, but the
displayed model sends that square to `C`, which has trace zero.
This proves the claimed failure of the additional relation and
keeps the four-word countermodel separate from the full exhaustion.
