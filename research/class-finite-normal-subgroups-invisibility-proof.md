---
rg: 2
id: class-finite-normal-subgroups-invisibility-proof
kind: route
title: Read off residual depth, stable length and support data as ambient class functions, and put rigid-stabilizer commutators inside the normal subgroup
target: class-finite-normal-subgroups-are-invisible-to-standard-hosts
requires: []
---

Notation as in the target: `N <| T` with finitely many `T`-classes.

## Master principle

A `T`-invariant function on `N` is constant on each `T`-class, so it takes at
most as many values as there are classes. Every item below exhibits a
`T`-invariant function and shows that, under the item's hypothesis, it would take
infinitely many values unless the stated conclusion holds.

## Item 1: residual depth

Let `N` be finitely generated, `M <= N` normal in `T`, and `P = N/M` residually
finite. Conjugation by `t in T` preserves `N` and `M`, so it induces an
automorphism of `P`.

- A finitely generated group has finitely many subgroups of index `<= k`: each
  is the stabilizer of a point in an action on at most `k` points, and such an
  action is determined by the images of the finitely many generators. So
  `P_k = ∩{H <= P : [P:H] <= k}` has finite index in `P`, and `P_k` is
  characteristic, since automorphisms permute the subgroups of index `<= k`.
- `P_1 >= P_2 >= ...` and `∩_k P_k = 1`, because `P` is residually finite and every
  finite-index subgroup has some index `k`.
- For `p in P`, `p != 1`, put `d(p) = min{k : p not in P_k}`. Since each `P_k`
  is characteristic, `d(t p t^-1) = d(p)`, and `x |-> d(xM)` is a `T`-invariant
  function on `N \ M`.
- If `P` is infinite then no `P_k` is trivial (each has finite index), so the
  chain never stabilizes (a stable value would equal the intersection `1`). So
  there are infinitely many `k` with `P_k != P_(k+1)`, and any
  `p in P_k \ P_(k+1)` has `d(p) = k + 1`. Hence `d` takes infinitely many
  values, a contradiction. So `P` is finite.

Apply this with `M = R(N)`: `R(N)` is characteristic in `N`, hence normal in `T`,
and `N/R(N)` is residually finite (an element outside `R(N)` lies outside some
finite-index subgroup containing `R(N)`). So `[N : R(N)] < infinity`. If
`K <| T` has finite index then `N ∩ K` has finite index in `N`, so it contains
`R(N)`, and the image `N/(N ∩ K)` of `N` in `T/K` has order at most `[N : R(N)]`.

## Item 2: stable length and quasimorphisms

Let `T` act by isometries on `(Y,d)`, `y in Y`, `x in T`.

- `a_m = d(x^m y, y)` is subadditive:
  `d(x^(m+n) y, y) <= d(x^(m+n) y, x^m y) + d(x^m y, y) = a_n + a_m`. By Fekete's
  lemma `tau(x) = lim a_m / m` exists.
- It does not depend on `y`: `|d(x^m y, y) - d(x^m z, z)| <= 2 d(y,z)`.
- It is a class function: `d(t x^m t^-1 y, y) = d(x^m t^-1 y, t^-1 y)`, so
  `tau(t x t^-1)` is `tau(x)` computed at the base point `t^-1 y`.
- It is homogeneous: `tau(x^k) = k tau(x)` for `k >= 1`, by passing to the
  subsequence `m k`.

If `x in N` had `tau(x) > 0`, the elements `x, x^2, x^3, ...` of `N` would have
pairwise distinct values of the `T`-invariant function `tau`. So `tau = 0` on
`N`. With `Y` the Cayley graph of a finitely generated `T`, `tau(x) = 0` says
`|x^m|_T = o(m)`.

A homogeneous quasimorphism `phi` with defect `D` satisfies
`|phi(t g^m t^-1) - phi(g^m)| <= |phi(t)| + |phi(t^-1)| + 2D` for all `m`, and
dividing by `m` gives `phi(t g t^-1) = phi(g)`. So `phi` is `T`-invariant with
`phi(x^k) = k phi(x)`, and the same argument gives `phi = 0` on `N`.

## The double-commutator lemma

Let `L <= Homeo(X)`, `X` Hausdorff, and `K <| L` with `K != 1`. For open `U`,
let `Rist_L(U)` be the elements of `L` that are the identity off `U`. Then there
is a nonempty open `U` with `[Rist_L(U), Rist_L(U)] <= K`.

*Proof.* Pick `n in K` and `x` with `n x != x`. Choose disjoint open `A ∋ x`,
`B ∋ n x` and put `U = A ∩ n^-1(B)`, open and containing `x`, with
`n(U) <= B` disjoint from `U`. Two homeomorphisms that are the identity off
disjoint sets `U`, `V` commute: each preserves its own set and fixes the other.
For `g, h in Rist_L(U)` put `g' = n g^-1 n^-1`, the identity off `n(U)`. Then
`c = [g, n] = g g' in K` and `g'` commutes with `g` and with `h`, so
`[c, h] = g g' h g'^-1 g^-1 h^-1 = g h g^-1 h^-1 = [g, h]`. As `c in K` and `K` is
normal, `[g, h] in K`. So all commutators of `Rist_L(U)`, hence the derived
subgroup, lie in `K`. `∎`

## Item 3: cone permutations

Let `rho` satisfy (CP) and suppose `rho(N) != 1`. `rho(N)` is normal in
`L = rho(T)`, so the lemma gives an open `U` with `[Rist_L(U), Rist_L(U)] <= rho(N)`.
For `k >= 2` take `D_1, ..., D_2k <= U`, `a`, `s` as in (CP); both lie in
`Rist_L(U)`. Put `b = s a^-1 s^-1`.

- `b` is the identity off `D_(k+1) ∪ ... ∪ D_2k`: for `y in D_1 ∪ ... ∪ D_k`,
  `s^-1 y` lies in `D_(k+1) ∪ ... ∪ D_2k`, where `a^-1` is the identity; for
  `y` off `D_1 ∪ ... ∪ D_2k`, all three maps fix `y`.
- `a` is the identity off `D_1 ∪ ... ∪ D_k`. So `a` and `b` commute.
- `a` has order exactly `k`: `a^k = 1`, and for `0 < j < k`, `a^j` maps the
  nonempty set `D_1` onto the disjoint set `D_(j+1)`. The same holds for `b`.
- Hence `[a, s] = a b` has order exactly `k`, and it lies in
  `[Rist_L(U), Rist_L(U)] <= rho(N)`.

The function `x |-> order of rho(x)` on `N` is `T`-invariant
(`rho(t x t^-1) = rho(t) rho(x) rho(t)^-1`), and it takes every value `k >= 2`.
This contradicts the master principle, so `rho(N) = 1`.

*(CP) for standard `V`.* A nonempty open `U <= {0,1}^N` contains a cone `C_w`.
Choose a length `m` with `2^m >= 2k` and distinct words `u_1, ..., u_2k` of length
`m`. Let `a` be the prefix replacement `w u_i -> w u_(i+1)` (`i < k`),
`w u_k -> w u_1`, and `s` the prefix replacement `w u_i <-> w u_(k+i)`, both the
identity on all other cones of the complete prefix code
`{w u : |u| = m} ∪ {v : |v| = |w|, v != w}`. These are elements of `V`, and
`D_i = C_(w u_i)` satisfies (CP).

## Item 4: interval bumps

Let `rho(T) >= F` in its standard action on `(0,1)` and suppose `rho(N) != 1`.
The lemma gives an open `U` with `[Rist_L(U), Rist_L(U)] <= rho(N)`, and
`Rist_F(U) <= Rist_L(U)`.

- *Bumps.* For dyadic `a < b` with `L = b - a`, the map equal to
  `x -> a + (x-a)/2` on `[a, a + L/2]`, `x -> x - L/4` on `[a + L/2, a + 3L/4]`,
  `x -> 2x - b` on `[a + 3L/4, b]`, and the identity elsewhere, is a
  piecewise-linear homeomorphism with dyadic breakpoints and slopes in `2^Z`,
  hence an element `f_[a,b]` of `F`. It satisfies `f(x) < x` on `(a,b)`, so its
  open support is exactly `(a,b)`.
- *A nontrivial commutator in a dyadic interval `J = [p, q] <= U`.* Pick dyadic
  `p < p' < r < q' < r' < q` and put `g = f_[p',q']`, `h = f_[r,r']`. The open
  support of `h g h^-1` is `h((p', q')) = (p', h(q'))` with `h(q') < q'`, which
  differs from `(p', q')`. So `h g h^-1 != g` and `c_J = [h, g] != 1`, and
  `c_J` is the identity off `J`.
- *Many components.* For `k >= 1` choose pairwise disjoint dyadic intervals
  `J_1, ..., J_k <= U` (dyadic rationals are dense) and `c = c_(J_1) ... c_(J_k)`.
  It lies in `[Rist_F(U), Rist_F(U)] <= rho(N)`. Its open support is the disjoint
  union of the nonempty open supports of the `c_(J_i)`, so it has at least `k`
  components; it has finitely many, because an element of `F` has finitely many
  breakpoints.

For a homeomorphism `phi` of `(0,1)`, the open support of `phi c phi^-1` is
`phi` of the open support of `c`, so the number of components of the open
support of `rho(x)` is a `T`-invariant function on `N`. It takes infinitely many
finite values, contradicting the master principle. So `rho(N) = 1`. `∎`

## Consequences for fiber-product data

These are derived in the target node from items 1--4 together with the free screen
of `fiber-product-conjugation-action-lemma` (a finite `N` with `C_T(N) = 1` forces
`T` finite), which is re-proved there in one line: `T` embeds in `Aut(N)` by
conjugation.
