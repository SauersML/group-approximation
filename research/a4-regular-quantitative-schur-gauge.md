---
rg: 2
id: a4-regular-quantitative-schur-gauge
kind: claim
title: Near intertwiners of regular A4 models are uniformly close to pure multiplicity gauges
---

Let `pi,pi'` be exact unitary representations of

```text
A4=<a,b | a^3=b^2=(ba)^3=1>
```

on the same finite-dimensional Hilbert space, and suppose both are the same
multiple of the regular representation.  For a unitary `U` put

```text
eta(U)=||U pi(a)-pi'(a) U||_2 + ||U pi(b)-pi'(b) U||_2.
```

There is a constant `C_A4<infinity`, depending only on the fixed generating
pair `(a,b)` and **not** on the regular multiplicity, such that one can find an
exact unitary `A4`-intertwiner `Z` with

```text
||U-Z||_2 <= C_A4 eta(U).                              (A4-SCHUR)
```

Moreover, on the canonical three-dimensional sectors from
`a4-coherence-fan-canonically-splits-multiplicity`, the exact intertwiner has
the form

```text
W' Z W^* = I_3 tensor V
```

for a unitary `V` between the multiplicity wires.  Consequently

```text
||W' R' U R W^* - I_3 tensor V||_2 <= C_A4 eta(U),
```

up to the harmless normalization change from the full space to the fixed
trace-`3/4` three-dimensional sector.

Thus an approximate overlap of two exact regular A4 contexts cannot hide a
matrix-valued distortion inside the local qutrit register: all dimension-growing
freedom is, quantitatively and uniformly, pushed onto a single multiplicity
unitary.