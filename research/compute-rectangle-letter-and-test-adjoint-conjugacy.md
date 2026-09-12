---
rg: 2
id: compute-rectangle-letter-and-test-adjoint-conjugacy
kind: route
title: Compute the normalized rectangle letter and refute formal adjoint conjugacy in the universal group
target: rectangle-adjoint-symmetry-is-an-extra-relation
requires:
  - rank-five-rectangle-is-one-letter-hecke-element
artifacts:
  - research/artifacts/five-seven-coefficient-and-adjoint-audit-2026-08-21.md
---

In the `F_4` corner, `(1+r)^-1=r e` and `(1+s)^-1=s e`.  Carrying out the
two edge normalizations gives `y=s^-1 h_0^-1 r^-1 x`.  The adjoint replaces
`y` by `y^-1`.  Specialize the same support equations to `C_3*<x>`: its
`C_3` normalizer is `C_3`, while cyclically reduced-word form rules out
`h(kx)h^-1=(kx)^-1` for every `h,k in C_3`.  Hence the desired conjugator is
not a formal consequence of the rectangle equations.

