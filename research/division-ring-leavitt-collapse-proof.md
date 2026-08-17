---
rg: 2
id: division-ring-leavitt-collapse-proof
kind: route
title: Both orthogonality relations invert, so the idempotent relation reads one plus one equals one
target: division-ring-hosts-no-binary-leavitt-family
requires: []
artifacts:
  - research/artifacts/strong-atiyah-audit-2026-08-17.md
---

## Why sufficient

Suppose `s_0, s_1, t_0, t_1` in a division ring `D` satisfy
`t_i s_j = delta_{ij}` and `s_0 t_0 + s_1 t_1 = 1`.

From `t_0 s_0 = 1` neither `t_0` nor `s_0` is zero, and in a division ring a
one-sided inverse is two-sided: `s_0 = t_0^{-1}`, hence `s_0 t_0 = 1`.  The
same argument at `i = 1` gives `s_1 t_1 = 1`.

Substituting into the idempotent relation:

    1 = s_0 t_0 + s_1 t_1 = 1 + 1,

so `1 = 0` and `D` is the zero ring, contrary to `D` being a division ring.

## Contrast worth keeping

`augmentation-blocks-unital-leavitt-family` reaches the same conclusion for
`ZG` and every `M_n(ZG)` and does **not** use the idempotent relation at all
-- there the orthogonality relations alone are contradictory after
augmenting.  Here the orthogonality relations are perfectly satisfiable in
isolation (take `s_i = t_i = 1`); it is the idempotent relation that breaks,
and it breaks precisely because invertibility forces both `s_i t_i` up to `1`.

The two mechanisms are complementary, and between them the unital Leavitt
route is closed into integral group rings and into skew fields alike -- the
two targets a Kaplansky or Atiyah argument would want.
