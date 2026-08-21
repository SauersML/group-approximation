---
rg: 2
id: leavitt-prefix-heisenberg-packet-proof
kind: route
title: Cancel reversed prefixes and apply finite Stone--von Neumann theory
target: leavitt-prefixes-form-exponential-heisenberg-packet
requires:
  - affine-active-corner-has-faithful-binary-leavitt-envelope
---

The reversed convention in `(LHP1)` places
`t_(alpha_n)s_(beta_n)` at the innermost position. Induction cancels equal
letters and gives zero at the first mismatch, proving `(LHP2)`.

Root additivity gives exponent `p` and commutation within each of the roots
`12` and `23`. The Steinberg commutator formula gives

```text
[x_12(t_alpha),x_23(s_beta)]
  =x_13(t_alpha s_beta),
```

which is `(LHP4)`. The root `13` commutes with both root families. Mapping to
upper unitriangular matrices shows that no extra relation collapses `J_A`.

On a nontrivial central-character sector, the group algebra of the resulting
finite Heisenberg group is a full matrix algebra of size `p^N`; equivalently,
finite Stone--von Neumann theory gives a unique simple module of dimension
`p^N`. This proves `(LHP5)`.
