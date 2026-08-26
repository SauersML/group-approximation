---
rg: 2
id: normal-kernel-restriction-rigidity-proof
kind: route
title: The identity is a K-intertwiner and the quotient acts trivially on intertwiners
target: normal-kernel-restriction-rigidity-for-map-free-quotients
requires: []
---

For `T in V`, `f in F`, `k in K`, normality gives `f^(-1) k f in K`, so
`u(k) Pi(f)(T) = u(f) u(f^(-1) k f) T v(f)^* = u(f) T v(f^(-1) k f) v(f)^*
= u(f) T v(f)^* v(k) = Pi(f)(T) v(k)`; thus `Pi(f)(T) in V`.  For `k in K`,
`Pi(k)(T) = u(k) T v(k)^* = T v(k) v(k)^* = T`, so `K` acts trivially and
`Pi|_V` is a finite-dimensional unitary representation of `Q`, which is
trivial by hypothesis.  If `u|_K = v|_K` then `1 in V`, and
`1 = Pi(f)(1) = u(f) v(f)^*` for all `f`.

(4): for `T in u(K)'`, `T` is a `K`-intertwiner from `u` to `u`, so by (1)
with `v = u` the operator `Pi(f)(T) = u(f) T u(f)^*` lies in `Hom_K(u, u)` and
the induced representation of `Q` on `Hom_K(u,u)` is trivial; hence
`u(f) T u(f)^* = T` for all `f`, i.e. `T in u(F)'`.  The reverse inclusion is
trivial, and bicommutants give `u(K)'' = u(F)''`.
