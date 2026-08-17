---
rg: 2
id: leavitt-kernel-annihilator-strict-self-embedding-proof
kind: route
title: Right multiplication by s_0 is onto and not injective; dualize
target: leavitt-kernel-annihilator-strict-self-embedding
requires: [leavitt-unit-group-algebra-surjects-onto-leavitt, leavitt-evaluation-kernel-hits-augmentation-one]
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

## Why sufficient

*The subshift.*  `S` is the direct sum of one copy of `F_2` per element of
`G`, so `S^*` is the product `F_2^G`.  Each `k` in `K` imposes the single
finite-support equation `sum_(g in supp k) c_g x(g) = 0`, whose solution set
is clopen, so `X = K^perp` is closed.  `K` is a left ideal, so
`x |-> x . ([h] . -)` preserves `X`: `X` is shift-invariant.  `K != 0` by
`leavitt-evaluation-kernel-hits-augmentation-one`, and a nonzero vector
carries a functional not annihilating it,
so `X` is **proper**.  Dually `X = im(pi^*)`, since a functional vanishes on
`K` exactly when it factors through `S/K ~ R`.

*The ring-level map.*  `M_(s_0) : R -> R`, `r |-> r s_0`, is `S`-linear for
the module structure through `pi`.  It is surjective because
`(r t_0) s_0 = r`, and not injective because `t_1 s_0 = 0` with `t_1 != 0`
(from `t_1 s_1 = 1`).  Dually `M_(s_0)^*` is injective — a dual of a
surjection — and not surjective: any functional nonzero at `t_1` kills no
element of the image, since every element of the image vanishes on
`ker M_(s_0)`.

*The local rule.*  With `x = s_0^2 t_1`, `y = s_1 t_0`, `z = s_0 s_1 t_1`,
the relations `t_1 s_0 = 0` and `t_0 s_1 = 0` give `x^2 = y^2 = z^2 = 0`, so
`u = 1+x`, `v = 1+y`, `w = 1+z` are units, self-inverse in characteristic
two.  Also `x y = s_0^2 (t_1 s_1) t_0 = s_0^2 t_0`, whence

    uv + u + v + w = (1 + x + y + xy) + (1+x) + (1+y) + (1+z)
                   = xy + z = s_0^2 t_0 + s_0 s_1 t_1
                   = s_0 (s_0 t_0 + s_1 t_1) = s_0.

(The four `1`s and the doubled `x, y` cancel in characteristic two.)  These
are the same square-zero moves the Lean proof of `unitAdditiveSpan_eq_top`
uses; the specialization is chosen to reach `s_0` in four units rather than
via all four corners.  The four group elements are distinct, since `x, y, z`
are distinct nonzero monomials in the prefix-code normal form and
`uv = 1 + x + y + xy` differs from each of `u, v, w`.

So `a = [uv] + [u] + [v] + [w]` in `S` has `pi(a) = s_0`, and the dual of
right multiplication `R_a : s |-> s a` is exactly

    (T_a x)(g) = x([g] a) = x(g uv) + x(g u) + x(g v) + x(g w),

a four-site linear cellular automaton.

*Transport.*  `pi(s a) = pi(s) s_0` says `pi . R_a = M_(s_0) . pi`.
Dualizing, `T_a . pi^* = pi^* . M_(s_0)^*`, so `T_a` preserves `X = im(pi^*)`
and its restriction is conjugate to `M_(s_0)^*` — injective and not
surjective, as required.
