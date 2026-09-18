---
rg: 2
id: unbounded-prime-torsion-via-counting-ring-steinberg
kind: route
title: The largest residually finite quotient of St_m over the counting ring, provided its finite residual is finitely normally generated
target: fp-rf-group-with-unbounded-prime-torsion
requires:
  - counting-ring-steinberg-group-has-every-torsion-order
  - counting-steinberg-residual-finitely-normally-generated
---

Let `R = R_count = Z<u,x,e | xu-ux-x, ue, eu>` and `r_n = e x^n e`. Take `m >= 4`
as in `counting-steinberg-residual-finitely-normally-generated`. Let
`G = St_m(R)`, and let `G_res` be its finite residual.

1. By (S1) of `counting-ring-steinberg-group-has-every-torsion-order`, `G` has a
   finite presentation `<X | Y>`.
2. By the open premise, `G_res` is the normal closure of finitely many elements
   `h_1, ..., h_s`. Write each `h_i` as a word in `X`. Then
   `Gamma = G / G_res = <X | Y, h_1, ..., h_s>` is finitely presented.
3. `Gamma` is residually finite. Every nontrivial element of `Gamma` lifts to an
   element `g` in `G` outside `G_res`. Some finite-index normal subgroup of `G`
   misses `g`, and it contains `G_res`, so it descends to `Gamma`.
4. By (S4), for every prime `p` the image of `x_12(r_p)` in `Gamma` has order
   exactly `p`. So `Gamma` has elements of unbounded prime order.

Hence `Gamma` is a finitely presented residually finite group with unbounded
prime torsion. It also has property (T), which the target does not need. `∎`

**Premise status.** The first premise is ESTABLISHED. The second is OPEN.
Mechanisms (M1) and (M2), recorded at the premise, are independent of each
other, and either one would close it.
