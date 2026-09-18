---
rg: 2
id: sl-2-q-root-group-is-parabolic-in-every-prime-factor-proof
kind: route
title: Direct proof via lattices, the one-tree dichotomy in each factor, and the horoball computation for u(t)
target: sl-2-q-root-group-is-parabolic-in-every-prime-factor
requires:
  - divisible-elements-act-elliptically-on-trees
  - gl-n-q-acts-faithfully-on-p-adic-bruhat-tits-buildings
  - cocompact-fg-stabilizer-actions-force-finite-generation
---

Direct proof. Not independently reviewed. Inputs from Serre, *Trees*, Ch. II §1:
the vertices of `T_p` are homothety classes of `Z_p`-lattices in `Q_p^2`; the ends
correspond equivariantly to the lines of `Q_p^2`; and for lattices `L, M` the
distance `d([L],[M])` is `|a - b|`, where `p^a, p^b` are the elementary divisors of
`M` relative to `L`.

## Vertices as global lattices

A `Z`-lattice `L ⊂ Q^2` gives the family `([L ⊗ Z_p])_p`, which is `o_p` for
almost all `p`. Conversely, given classes `[M_p]` with `M_p = Z_p^2` for almost all
`p`, the lattice `L = ∩_p (M_p ∩ Q^2)` has `L ⊗ Z_p = M_p`. Two lattices with the
same local classes differ by `∏ p^(a_p) ∈ Q^x`. So vertices of `X` are lattices
modulo `Q^x`, equivariantly.

## Part 1

The orbit counts are item 3 of `cocompact-fg-stabilizer-actions-force-finite-generation`.

- **Stabilizers.** If `g ∈ SL_2(Q)` and `g L = r L`, comparing covolumes gives
  `r^2 = 1`, so `g L = L`. Hence `Stab([Z^2]) = SL_2(Z)`.

## Part 2

- **No fixed vertex.** Fix `p`. The vertex `o_p` is moved by `u(1/p)`, because
  `u(1/p) Z_p^2 ≠ Z_p^2`. The subgroup `u(Z[1/p]) ≤ U` has unbounded orbits on
  `T_p`: by the computation in Part 4, `d(o_p, u(p^-e) o_p) = 2e`. So `U` fixes no
  vertex of `T_p`.
- **Exactly one end.** The vertex stabilizers of `SL_2(Q)` on `T_p` are
  residually finite (`gl-n-q-acts-faithfully-on-p-adic-bruhat-tits-buildings`,
  Part 3). So by part 3 of `divisible-elements-act-elliptically-on-trees`, `U`
  fixes exactly one end of `T_p`. It fixes the end of `Q_p e_1`, since
  `u(t) e_1 = e_1`.
- **Product.** Fixed points in `∏_p (T_p ∪ ∂T_p)` are taken coordinatewise.
- **Stabilizer.** `g ∈ SL_2(Q)` fixes `ξ_p` iff `g(Q_p e_1) = Q_p e_1`. Since
  `g e_1 ∈ Q^2`, this happens iff `g e_1 ∈ Q e_1`, i.e. iff `g ∈ B(Q)`.

## Part 3

Let `y_j = [Z_p e_1 ⊕ p^j Z_p e_2]` for `j ∈ Z`, a geodesic line in `T_p` whose
positive end is `ξ_p`. The element `g = [[a, b], [0, a^-1]]` fixes `ξ_p`, and
`diag(a, a^-1) y_j = [a Z_p e_1 ⊕ a^-1 p^j Z_p e_2] = y_(j - 2 v_p(a))`. The unipotent
factor `u(b/a)` fixes `y_j` for all large `j` (Part 4). So `g` moves points far out
along the ray to `ξ_p` by `2 v_p(a)` steps toward the negative end. Its Busemann
value is therefore `2 v_p(a)` up to one global sign convention. `β` is a
homomorphism on `B(Q)` (Busemann functions of a fixed end), with the stated image
and with kernel `{a = ±1} = ±U`.

## Part 4

Let `t ∈ Q^x` with `v_p(t) = -e < 0`. Then `u(t)(p^j e_2) = t p^j e_1 + p^j e_2`,
so `u(t)` fixes `y_j` iff `j >= e`. Its fixed set in `T_p` is a subtree containing
`y_e, y_(e+1), ...` but not `y_0, ..., y_(e-1)`. For a subtree `F` of a tree, every
geodesic from `y_0` to a point of `F` passes through the projection of `y_0` onto
`F`. Applied to `y_e`, this shows the projection is `y_e`, at distance `e`. For an
elliptic tree automorphism, `d(y, g y) = 2 d(y, Fix g)`, so
`d(o_p, u(t) o_p) = 2e`. If `v_p(t) >= 0`, `u(t)` fixes `o_p`.

For `t = 1/m!`, `v_p(t) = -v_p(m!)`, which is negative exactly for `p <= m`. The
distance in `X` is the sum of the factor distances. So:

- `Fix_X(U_m) = ∏'_p Fix_(T_p)(u(1/m!))`, with nearest vertex
  `x_m = (y^(p)_(v_p(m!)))_p`, the class of `Z e_1 ⊕ m! Z e_2`;
- `d(o, x_m) = Σ_p v_p(m!) = Ω(m!)`, and `d(o, u(1/m!) o) = 2Ω(m!)`.

The coordinates of `x_m` increase with `m` along each ray, so the distances add up
and `d(x_(m-1), x_m) = Σ_p v_p(m) = Ω(m)`. A matrix `u(t)` fixes
`Z e_1 ⊕ m! Z e_2` iff `m! t ∈ Z`, so `U ∩ Stab(x_m) = U_m`.

**Bounds.** `Ω(m!) = Σ_(k=2)^m Ω(k) >= m - 1`, since `Ω(k) >= 1` for `k >= 2`.
Also `2^(Ω(m!)) <= m! <= m^m`.

## Hosts

For `h = f_1 ... f_l` with `f_k ∈ F^(±1)`, the triangle inequality and invariance
give `d(y, h y) <= Σ_k d(y, f_k y)`, which is at most `l C` at `y = ι o`. With
`h = u(1/m!)`, `d_M(ι o, h ι o) = d_X(o, h o) = 2Ω(m!)`. Also `C > 0`: otherwise every generator fixes `ι o`, so `H` does, but `u(1/2)`
moves `ι o` (it moves `o`, and `ι` is isometric). The coarse version is the same computation.
