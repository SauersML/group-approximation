---
rg: 2
id: stw96-fibrewise-nowhere-scattered-generator-obstruction
kind: claim
title: A nowhere-scattered C(X)-field with one obstructed fibre is not singly generated
artifacts:
  - research/artifacts/stw96-xcvi-xcvii-literature-audit-2026-08-30.md
---

Let `X` be a compact Hausdorff space and let `E` be a unital `C(X)`-algebra.
Write

```text
E_x = E / C_0(X minus {x})E
```

for its fibre at `x`.  If every fibre `E_x` is nowhere scattered, then `E` is
nowhere scattered.  If, in addition, one fibre `E_x0` contains a finite set
which is contained in no singly generated subalgebra of `E_x0`, then arbitrary
lifts of that set form the same obstruction in `E`; in particular, `E` is not
singly generated.

Consequently, if `A` is the Elliott--Li--Niu AH algebra and `X` is any nonempty
compact metrizable space, then

```text
D_X = C(X) tensor_min A
```

is a unital separable nuclear nowhere-scattered C*-algebra which is not singly
generated.  The fixed Elliott--Li--Niu obstruction lifts as `1 tensor F`.  Its
centre is `C(X) tensor 1`; hence `D_X` is non-simple whenever `X` has at least
two points.  This supplies counterexamples over connected bases such as every
cube `[0,1]^d`, not merely finite direct sums of the simple example.
