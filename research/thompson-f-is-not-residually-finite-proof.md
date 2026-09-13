---
rg: 2
id: thompson-f-is-not-residually-finite-proof
kind: route
title: A displaced conjugate kills a commutator in every finite quotient of F
target: thompson-f-is-not-residually-finite
requires: []
---

**Model.** `F` is the group of piecewise-linear homeomorphisms of `[0,1]` with
finitely many breakpoints, all at dyadic rationals, and all slopes integer powers
of 2 (Cannon–Floyd–Parry §1). Its standard generators are:

- `x_0`: equal to `t/2` on `[0,1/2]`, `t − 1/4` on `[1/2,3/4]`, and `2t − 1` on
  `[3/4,1]`;
- `x_1`: the identity on `[0,1/2]`, and on `[1/2,1]` the same shape as `x_0`
  rescaled to that interval.

They do not commute. Conjugation gives `x_0^{-1} x_1 x_0 = x_2`, whose support is
`(3/4,1)`, while `x_1` has support `(1/2,1)`.

**Step 1: a local non-commuting pair.** Let `phi(t) = t/4 + 1/4`, an affine map
`[0,1] → [a,b] = [1/4,1/2]` with slope `2^{-2}` and dyadic translation. For
`f ∈ F`, the map equal to `phi f phi^{-1}` on `[a,b]` and to the identity elsewhere
is PL, has dyadic breakpoints (the images of `f`'s breakpoints, together with `a`
and `b`), and has slopes powers of 2. So it lies in `F`. Put `g_1`, `g_2` for the
elements obtained from `x_0` and `x_1`. They are supported in `[a,b]`, and they do
not commute because `x_0` and `x_1` do not. So `c = [g_1, g_2] ≠ 1`.

**Step 2: a displacing element.** Every point `t ∈ (0,1)` satisfies `x_0(t) < t`.
So `x_0^{-1}(t) > t` on `(0,1)`, and `x_0^{-n}(t) → 1` as `n → ∞`. Choose `n` with
`x_0^{-n}(1/4) > 1/2`, and put `h = x_0^{-n}`. Then `h(t) > t` on `(0,1)` and
`h(a) > b`. By induction `h^i(a) = h^{i-1}(h(a)) > h^{i-1}(b)`, so the intervals
`h^i[a,b]` (`i >= 0`) are pairwise disjoint.

**Step 3: every finite quotient kills `c`.** Let `N` be a normal subgroup of `F`
of finite index `m`.

1. Among `h^0, …, h^m` two agree modulo `N`, so `h^j ∈ N` for some
   `1 <= j <= m`.
2. Put `g_2' = h^j g_2 h^{-j}`. It is supported in `h^j[a,b]`, which is disjoint
   from `[a,b]`, the support of `g_1`. So `[g_1, g_2'] = 1`.
3. `g_2' g_2^{-1} = [h^j, g_2] = h^j (g_2 h^{-j} g_2^{-1})`, a product of two
   elements of `N`. So `g_2' ≡ g_2 (mod N)`.
4. Hence `c = [g_1, g_2] ≡ [g_1, g_2'] = 1 (mod N)`, that is, `c ∈ N`.

The element `c` depends only on `g_1` and `g_2`, not on `N`. So the nontrivial
element `c` lies in every finite-index normal subgroup, and `F` is not residually
finite.

**Corollary.** If `F` were isomorphic to a subgroup of a residually finite group
`G`, intersecting finite-index normal subgroups of `G` with that subgroup would
separate `c` from 1. So residually finite groups contain no copy of `F`.

**Model test.** The argument needs a non-commuting pair supported in an interval
that some group element displaces off itself. In the residually finite group
`Z ≀ Z`, every displaceable local subgroup is abelian, so Step 1 has no analogue,
and indeed `Z ≀ Z` is residually finite.
