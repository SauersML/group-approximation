---
rg: 2
id: k0-hahn-banach-from-traces-and-boundary
kind: route
title: Unitize, make all traces quasidiagonal, kill sign changes, and settle the boundary
target: every-separable-nuclear-qd-algebra-has-k0-hahn-banach
requires: [amenable-traces-on-exact-cstar-algebras-are-quasidiagonal, stw07-sign-changing-qd-trace-values-kill-class, stw07-singular-classes-change-sign-or-sit-on-boundary, k0-hahn-banach-for-boundary-singular-classes]
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

1. **Unital reduction.**  For nonunital `A`, `K_0(A)` embeds split-injectively
   in `K_0(A~)`.  If `nx = [p]` with `p in M_N(A~)`, the scalar image of `p` is
   a rank-zero projection, so `p in M_N(A)`.  Thus a singular class stays
   singular in `A~`, and faithful models of `A~` killing `x` restrict to
   faithful models of `A` killing `x`.
2. **All traces quasidiagonal.**  `A~` is separable, nuclear and
   quasidiagonal; its traces are amenable, and by the exact X(1) residual they
   are quasidiagonal.
3. **Sign pattern.**  By the boundary theorem, a singular class is not strictly
   one-signed on traces.  If it takes both strict signs, the sign-changing
   theorem kills it; otherwise it is a boundary class (after replacing `x` by
   `-x`), and the boundary claim kills it.
