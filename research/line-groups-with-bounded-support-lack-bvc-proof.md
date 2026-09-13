---
rg: 2
id: line-groups-with-bounded-support-lack-bvc-proof
kind: route
title: "The number of support components is a power-stable conjugacy invariant, and disjoint translates make it unbounded"
target: line-groups-with-bounded-support-lack-bvc
requires: []
---

`Homeo^+(R)` is torsion-free: if `h(x) > x` then `h^n(x) > x` for all `n >= 1`.
So by von Puttkamer--Wu Corollary 1.5 (arXiv:1607.03790v2), if `G` had BVC
there would be `g_1, ..., g_n` with every element of `G` conjugate to a power
of some `g_i`.

For `h` in `G` let `kappa(h)` be the number of components of `supp(h)`, in
`{0, 1, 2, ..., infinity}`.

1. `kappa` is a conjugacy invariant: `supp(x h x^{-1}) = x(supp h)`.
2. `supp(h^m) = supp(h)` for `m != 0`.  Fixed points of `h` are fixed by `h^m`.
   If `h(x) > x`, monotonicity gives `h^m(x) > x` for `m > 0`, and
   `h^{-1}(x) < x` (otherwise `x = h(h^{-1}x) >= h(x) > x`), so `h^m(x) < x` for
   `m < 0`; the case `h(x) < x` is symmetric.
3. By 1 and 2, `kappa` takes values in the finite set
   `{0} union {kappa(g_i)}` on all of `G`.
4. Let `supp(g)` lie in `(a, b)` with `kappa(g) = c`, `1 <= c < infinity`.  The
   orbit `G.a` is unbounded above: `s = sup G.a` is `G`-invariant, since each
   element is an increasing homeomorphism, so `s < infinity` would be a global
   fixed point.  Pick `h` in `G` with `h(a) > b`.  Then `h((a,b))` lies to the
   right of `(a,b)`, and applying the increasing map `h` repeatedly, the
   intervals `h^j((a,b))` for `j = 1, ..., k` are pairwise disjoint.
5. Put `P_k = prod_{j=1}^{k} h^j g h^{-j}`.  The factors have supports
   `h^j(supp g)` inside the disjoint intervals `h^j((a,b))`, so they commute and
   `supp(P_k)` is their disjoint union.  Hence `kappa(P_k) = k c`.

For large `k`, `k c` exceeds every finite value in the set of step 3.  This
contradicts BVC.  For `[0,1]` apply the argument to `(0,1)`, which is
homeomorphic to `R`.  `∎`
