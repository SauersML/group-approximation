---
rg: 2
id: property-t-free-leavitt-via-jacobson-head-root
kind: route
title: Embed the one-branch Jacobson Steinberg cover and normally saturate its head root
target: property-t-free-leavitt-full-mf-radical
requires:
  - binary-jacobson-steinberg-head-root-is-mf-invisible
  - full-leavitt-idempotent-defect-saturation
---

The coefficient assignment

```text
S->s_0,              T->t_0
```

embeds the Jacobson ring `J` in `R=L_(F_2)(1,2)`: the orbit quotient from
`leavitt-first-offdiagonal-packet-has-jacobson-orbit-quotient` is a left
inverse.  Functoriality and rank stabilization give a homomorphism

```text
St_5(J) -> St_20(R)
```

which sends

```text
x_13(1-ST) -> x_13(1-s_0t_0)=x_13(s_1t_1)=z.
```

Restrict any norm-corona homomorphism of `St_20(R)` along this map.  The
first prerequisite kills `z`.  The second prerequisite says that `z`
normally generates the full Steinberg target, so the original homomorphism
is trivial and its MF radical is the whole group.
