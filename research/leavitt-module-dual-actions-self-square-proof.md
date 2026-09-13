---
rg: 2
id: leavitt-module-dual-actions-self-square-proof
kind: route
title: Dualize L ≅ L ⊕ L, count unipotent translates for ergodicity, and fix s_0 m by a corner copy of U
target: leavitt-module-dual-actions-are-self-squares-off-bernoulli
requires:
  - bernoulli-factor-algebraic-actions-have-finite-stabilizers
---

Notation as in the target. For a word `u = u_1...u_n` put `s_u = s_(u_1)...s_(u_n)` and
`t_u = t_(u_n)...t_(u_1)`. Induction on `n` gives `t_v s_u = delta_(u,v)` for `|u| = |v| = n`, and
`sum over |v| = n of s_v t_v = 1`. Duality facts are as in
`stable-finiteness-algebraic-bernoulli-absorption-proof`.

**1. Self-square.** Right multiplications are left `L`-linear. Put `phi(a) = (a s_0, a s_1)` and
`psi(a, b) = a t_0 + b t_1`. Then `psi(phi(a)) = a (s_0 t_0 + s_1 t_1) = a`, and
`phi(psi(a, b)) = ((a t_0 + b t_1) s_0, (a t_0 + b t_1) s_1) = (a, b)`. So `L ≅ L ⊕ L` as left
`L`-modules, hence as `F_2[U]`-modules. Dualizing gives an equivariant continuous group isomorphism
`X_L ≅ X_L × X_L`, which preserves Haar measure.

**2a. Every nonzero right ideal `yL` is infinite.** Let `y != 0` and `n >= 1`. From
`y = sum over |v| = n of y s_v t_v`, some `y s_v != 0`. If `sum over |w| = n of c_w y s_v t_w = 0`,
right multiplication by `s_(w')` gives `c_(w') y s_v = 0`, so `c_(w') = 0`. So `yL` contains `2^n`
linearly independent elements, for every `n`.

**2b. Essential freeness.** For `u != 1`, `u.x = x` means `x((u^-1 - 1)a) = 0` for all `a`, so
`Fix(u) = Ann(S)` with `S = (u^-1 - 1)L`, which is infinite by 2a. `X_L / Ann(S)` is the dual of `S`,
an infinite group. So `Ann(S)` has infinitely many disjoint translates of equal Haar measure, and
measure `0`. `U` is countable, so almost every point has trivial stabilizer.

**2c. Ergodicity.** The characters `chi_a(x) = (-1)^(x(a))`, `a in L`, form an orthonormal basis of
`L²(X_L)`, and `(u.chi_a)(x) = chi_a(u^-1.x) = (-1)^(x(ua))`, so `u.chi_a = chi_(ua)`. An invariant
`f = sum c_a chi_a` has `c` constant on `U`-orbits, and square-summability kills `c` on infinite
orbits. It remains to show that every `a != 0` has an infinite orbit.
- For `|u| = |v| = n` with `u != v`, `e_(uv) = s_u t_v` satisfies `e_(uv)² = s_u (t_v s_u) t_v = 0`,
  so `1 + e_(uv)` is a unit, its own inverse in characteristic `2`.
- Fix `n`. From `a = sum over |v| = n of s_v t_v a`, choose `v` with `y = t_v a != 0`.
- The units `1 + e_(uv)` send `a` to `a + s_u y`. If `s_u y = s_(u') y`, applying `t_u` gives
  `y = delta_(u,u') y`, so `u = u'`.

So the orbit of `a` has at least `2^n - 1` elements, for every `n`.

**3. Off the Bernoulli world.** Let `M != 0` be an `L`-module and `m != 0` in `M`.
- `t_0 (s_0 m) = m`, so `s_0 m != 0`.
- For `b in U` put `iota_1(b) = s_0 t_0 + s_1 b t_1`. Since `t_0 s_1 = t_1 s_0 = 0`,
  `iota_1(b) iota_1(b') = iota_1(b b')` and `iota_1(1) = 1`. So `iota_1: U -> U` is a homomorphism,
  injective because `t_1 iota_1(b) s_1 = b`.
- `iota_1(b) s_0 m = s_0 (t_0 s_0) m + s_1 b (t_1 s_0) m = s_0 m`.
- `U` is infinite: the units `1 + e_(uv)` of 2c are pairwise distinct.

So `Stab_U(s_0 m)` contains the infinite group `iota_1(U)`, and
`bernoulli-factor-algebraic-actions-have-finite-stabilizers` shows that `X_M` is not a factor of a
Bernoulli shift. If `X_M × B ≅ B'`, the projection makes `X_M` a factor of `B'`, which is excluded.
