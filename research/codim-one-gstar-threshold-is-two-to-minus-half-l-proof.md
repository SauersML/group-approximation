---
rg: 2
id: codim-one-gstar-threshold-is-two-to-minus-half-l-proof
kind: route
title: Dualise hyperplanes to edges and codimension-two spaces to lines, so that GStar cost is carried only by triangles of a rainbow graph, cap triangles by tr A^3, build violators from a Sidon clique on a heavy star, and lift to every n along a projection with an honest zero table off the injective locus
target: codim-one-gstar-threshold-is-two-to-minus-half-l
requires: []
artifacts:
  - experiments/ugc-gstar-rainbow-2026-09-17/check_codim1_gstar_threshold.py
---

Notation is that of the target. `<x, u>` is the standard dot product on
`F_2^n`. Every linear functional on a subspace `S` is `u -> <x, u>` for some
`x`, and `x, x'` give the same functional on `S` iff `x + x' in S^perp`. So
functionals on `S` are the cosets of `S^perp`.

## Step 1: the dictionary at n = l+1

Put `d := n = l+1`. A hyperplane `S` equals `nu^perp` for a unique
`nu != 0`, and `S^perp = {0, nu}`. So `F(S)` is a pair `e_nu = {x, x+nu}`: an
edge of the complete graph on `F_2^d` whose *colour* `x + (x+nu)` is `nu`.
Distinct colours give distinct edges. The family `G_F := {e_nu}` is therefore
a simple graph with exactly one edge of each of the `m = 2^d - 1` colours,
a *rainbow graph*, and every rainbow graph arises.

An `(l-1)`-space `W` equals `P^perp` for a unique 2-dimensional `P`, and
`F(W)` is a coset `C_W` of `P`, a 4-point set. We have `W <= nu^perp` iff
`nu in P`. There are `N = m(m-1)/6` such `P`.

**(1a) Value.** Given `W`, `u notin W` means `S := W + u` is one of the three
hyperplanes `nu^perp`, `nu in P \ 0`, with `u in S \ W`. Each has
`|S \ W| = 2^(l-1)`, so each has probability `2^(l-1)/2^(l+1) = 1/4`, and
given `S` the vector `u` is uniform on `S \ W`. Restriction from `S` to `W` is
the map of cosets `x + <nu> -> x + P`. So `F(S)|_W = F(W)` iff `e_nu` lies in
`C_W`. With `s(W)` the number of such `nu`, `Pr_u[u notin W, sat] = s(W)/4`
and `val(F) = sum_W s(W)/(4N)`.

**(1b) Cost.** Fix `psi in F_2^d` and a satisfied `nu in P`, and pick
`x in e_nu`. On `u in S \ W` the event `F(S)(u) != psi(u)` is
`<x + psi, u> = 1`. Put `delta := x + psi`.

* If `delta in <nu>`, that is `psi in e_nu`, then `delta` vanishes on `S`.
  The cost is 0.
* If `delta in P \ <nu>`, that is `psi in C_W \ e_nu`, then `delta` vanishes
  on `W = P^perp` but not on `S`. So `<delta, u> = 1` on all of `S \ W`, and
  the cost is 1.
* If `delta notin P`, then `delta` is nonzero on `W`. Writing
  `S \ W = u0 + W`, the bit `<delta, u0 + w>` is balanced over `w`, and the
  cost is 1/2.

So `Pr_u[u notin W, sat, F(S)(u) != psi(u)] = (1/4) sum_(sat nu) c_nu(psi)`,
with `c_nu(psi)` equal to 0, 1 or 1/2 in the three cases.

**(1c) Meeting lemma.** Let `a != b` lie in `P`. A colour-`a` edge and a
colour-`b` edge meet iff they lie in the same `P`-coset.

*Proof.* If they share `x`, both lie in `x + P`. Conversely, inside
`C = y + P` take the colour-`a` edge `{y, y+a}` (every colour-`a` edge in `C`
has this form for some `y in C`) and a colour-`b` edge `{z, z+b}` in `C`. Then
`z` is one of `y, y+a, y+b, y+a+b`. In the first two cases `z` is common. If
`z = y+b` then `z+b = y` is common, and if `z = y+a+b` then `z+b = y+a` is
common. QED

Meeting is therefore an equivalence relation on `{e_a, e_b, e_(a+b)}`
(same coset), so a line has 0, 1 or 3 meeting pairs. Three pairwise meeting
edges of distinct colours either share a vertex (a **star**, type FU) or form
a **triangle** (type FT). One meeting pair is type t, none is type s1.

**(1d) Minimum cost at W.** If the satisfied edges at `W` have a common
vertex `psi`, then `psi` has cost 0. This covers every `W` with `s(W) <= 1`,
every `W` with `s(W) = 2` (both satisfied edges lie in `C_W`, so they meet by
1c), and every star. For a satisfied triangle every `psi` pays:

* a triangle vertex lies on two of the edges and pays `(1/4)(0 + 0 + 1) = 1/4`;
* the fourth point of `C_W` pays `3/4`;
* any `psi notin C_W` pays `3/8`.

So the minimum is `1/4`, and

```text
D(F) = #{ W : s(W) = 3, triangle } / (4N).                                   (1)
```

## Step 2: Theorem A

A line of type FT is a triangle `{x, y, z}` of `G_F`. Conversely, a triangle
of `G_F` has colours `x+y`, `y+z`, `x+z`, which form a line, and that line
carries only the three edges of those colours. So FT lines and triangles of
`G_F` correspond bijectively, and (1) gives `D(F) <= T(G_F)/(4N)`.

Let `A` be the adjacency matrix of `G_F`, with eigenvalues `lambda_i`. Then
`6T = tr A^3 = sum lambda_i^3 <= max|lambda_i| * sum lambda_i^2`. Also
`sum lambda_i^2 = tr A^2 = 2m`, so `max|lambda_i| <= sqrt(2m)`. Hence
`T <= (2m)^(3/2)/6 = (sqrt2/3) m^(3/2)`, and

```text
D(F) <= (sqrt2/3) m^(3/2) / (4 m (m-1)/6) = (sqrt2/2) m^(1/2)/(m-1) = delta(l).
```

With `m = 2^(l+1) - 1`, `m - 1 >= (3/4) 2^(l+1)` for `l >= 2` and
`m^(1/2) <= 2^((l+1)/2)`, so `delta(l) <= (sqrt2/2)(4/3) 2^(-(l+1)/2) = (2/3) 2^(-l/2)`.

If `L_max >= 2^(l+1)`, take `Psi` to be all functionals. Then
`D_Psi(F) = D(F) <= delta(l) = gamma - (gamma - delta(l))` for every `F`,
which is GStar_(l+1)(gamma, gamma - delta(l)). It is non-vacuous when
`gamma > delta(l)`.

A violator at `gamma` needs `gamma <= D(F) <= delta(l)`, so
`gamma*_(l+1) <= delta(l)`.

## Step 3: line-type bookkeeping

Let `f`, `t`, `s1` count lines of types FT or FU, t, and s1, so
`N = f + t + s1`. Choose `F(W)` to be a `P`-coset holding the most edges of
`P`'s colours. By 1c, full lines get `s = 3`, t-lines get `s = 2` (the coset
of the meeting pair) and s1-lines get `s = 1`. So

```text
sum_W s(W) = 3f + 2t + s1 = N + 2f + t.                                     (2)
```

Every pair of meeting edges has distinct colours `a, b` and lies on the line
`{a, b, a+b}`. Full lines carry 3 meeting pairs, t-lines 1 and s1-lines 0, so

```text
Pi := sum_v C(deg v, 2) = 3f + t,   hence   2f + t >= (2/3) Pi.             (3)
```

Every FT line gets `s = 3` under this choice, so by (1)
`D(F) = T(G_F)/(4N)`.

## Step 4: Theorem B

**(4a) The Sidon set.** Let `h := floor(d/2)` and identify `F_(2^h)^2` with a
subspace of `F_2^d`. The set `{(x, x^3) : x in F_(2^h)}` has `2^h` elements
and contains `0`. It is Sidon: suppose `(x,x^3) + (y,y^3) = (z,z^3) + (w,w^3)`
with `x != y`. Then `a := x + y = z + w != 0`, and in characteristic 2,
`x^3 + y^3 = a(x^2 + xy + y^2) = a(a^2 + xy)`. So `xy = zw`, and `{x, y}` and
`{z, w}` are both the root set of `X^2 + aX + xy`. Since
`2^h >= 2^(l/2) >= sigma`, a Sidon set `S'` of size `sigma = floor(2^(l/2))`
containing `0` exists. Any subset of a Sidon set is Sidon.

**(4b) The graph.** Put `A := S' \ {0}`, `Sigma(A) := {a + b : a != b in A}`
and `Sigma(S') := A u Sigma(A)`. Because `S'` is Sidon:

* the `C(sigma, 2)` sums of pairs of `S'` are distinct and nonzero;
* `Sigma(A)` has `C(sigma-1, 2)` elements;
* `Sigma(A)` misses `A`, since `a + b = c + 0` would force `{a,b} = {c,0}`.

`G` has the edges `{a, b}` for `a != b in S'`, which use the colours
`Sigma(S')` once each, and the edges `{0, z}` for every
`z notin Sigma(S') u {0}`. Such a `z` is not in `S'`, because `A` lies in
`Sigma(S')`, so these edges are new. Hence `G` is rainbow.

The neighbours of `0` are `A` together with the complement of
`Sigma(S') u {0}`. That is exactly the set of nonzero vectors outside
`Sigma(A)`, so `deg 0 = M := m - C(sigma-1, 2)`. Every vertex outside `S'`
has degree at most 1, so it lies in no triangle. Hence the triangles of `G`
are exactly the `C(sigma, 3)` triangles of the clique on `S'`.

**(4c) The count.** With the choice of Step 3, (2), (3) and
`Pi >= C(M, 2)` give

```text
sum_W s(W) - 2N  =  2f + t - N  >=  (2/3) C(M,2) - N,      D(F) = C(sigma,3)/(4N).
```

Since `N = C(m,2)/3`, we get `val(F) - 1/2 >= D(F)` as soon as

```text
2 C(M,2) - C(m,2)  >=  3 C(sigma,3).                                          (4)
```

Then `F` is a violator at `gamma_B = D(F) = C(sigma,3)/(4N) = 3C(sigma,3)/(4C(m,2))`.

**(4d) Proof of (4) for l >= 4.** Put `X := 2^d = 2^(l+1) >= 32`. From
`sigma^2 <= 2^l = X/2` we get `C(sigma-1,2) <= sigma^2/2 <= X/4`, so
`M >= m - X/4 = 3X/4 - 1`. Then

```text
2C(M,2) - C(m,2)  >=  (3X/4 - 1)(3X/4 - 2) - (X-1)(X-2)/2  =  X^2/16 - 3X/4 + 1,
3C(sigma,3)       <=  sigma^3/2  <=  (X/2)^(3/2)/2  =  X^(3/2)/2^(5/2).
```

Let `g(X) := 1/16 - 3/(4X) + 1/X^2 - X^(-1/2)/2^(5/2)`, which is the
difference divided by `X^2`. Its derivative
`3/(4X^2) - 2/X^3 + X^(-3/2)/2^(7/2)` is positive for `X > 8/3`. At `X = 32`,
`X^2 g(X) = 64 - 24 + 1 - 32 = 9 > 0`, using `32^(3/2)/2^(5/2) = 2^(15/2 - 5/2) = 32`.
So (4) holds for every `l >= 4`.

**(4e) Size of gamma_B.** We have `3C(sigma,3) = sigma(sigma-1)(sigma-2)/2`
and `4C(m,2) = 2m(m-1) < 2^(2l+3)`, so
`gamma_B > sigma(sigma-1)(sigma-2) / 2^(2l+4)`. For `l >= 8`:

* `sigma >= 16` and `sigma > 2^(l/2) - 1 >= (15/16) 2^(l/2)`;
* `(1 - 1/sigma)(1 - 2/sigma) >= (15/16)(7/8)`.

Hence `sigma(sigma-1)(sigma-2) >= (15/16)^4 (7/8) 2^(3l/2) >= 0.67 * 2^(3l/2)`,
and `gamma_B > 0.67 * 2^(-l/2)/16 >= 2^(-l/2)/32`. As `l -> infinity`,
`sigma/2^(l/2) -> 1`, `m(m-1) ~ 2^(2l+2)`, and `gamma_B 2^(l/2) -> 1/16`.

`gamma_B > 2^(1-l)` holds as soon as `2^(l/2) > 64`, that is for `l >= 13`
from this bound alone. The exact value exceeds `2^(1-l)` already at `l = 12`
(`gamma_B 2^(l/2) = 0.0596 > 2^(1-l/2) = 0.03125`). The artifact tabulates
`gamma_B` for `l = 4..199`.

The corollary's lower bound `gamma*_(l+1) >= gamma_B(l) >= 2^(-l/2)/32` for
`l >= 8` follows. For `4 <= l <= 7` the artifact gives
`gamma_B(l) 2^(l/2) >= 0.0217`.

## Step 5: Theorem C (lift to every n)

Let `n >= d = l+1` and `l >= 2`. Let `phi : F_2^n -> F_2^d` be onto, with
kernel `K` of dimension `n - d`. For a subspace `S` of dimension `l` or
`l-1`, put `F(S) := F0(phi S) o phi|_S` if `S` meets `K` only in `0` (then
`phi|_S` is injective and `phi S` has the dimension of `S`), and
`F(S) := 0`, the zero functional, otherwise. For a fixed `W`, write
`val_W := Pr_u[u notin W, sat]` and `D_W := min_psi Pr_u[u notin W, sat, F(W+u)(u) != psi(u)]`.
At dimension `d` write `val0_(W0)` and `D0_(W0)` for the same quantities of
`F0`. So `val(F) = E_W val_W`, `D(F) = E_W D_W`, and similarly for `F0`.

**(5a) W meets K.** Then every `S = W + u` also meets `K`, so
`F(S) = 0 = F(W)`. Every `u notin W` is satisfied, and `F(S)(u) = 0`. So
`val_W = 1 - 2^(l-1-n)` and `D_W = 0` (take `psi = 0`).

**(5b) W meets K only in 0.** Put `W0 := phi W`, an `(l-1)`-space of
`F_2^d`, and `v := phi(u)`. Since `phi` is onto, `v` is uniform on `F_2^d`,
and given `v` the vector `u` is uniform on the coset `phi^(-1)(v)` of `K`.

* If `v notin W0`, then `S := W + u` meets `K` only in `0`. Indeed, if
  `phi(w + eps u) = 0` with `w in W`, then `eps = 1` would give
  `v = phi(w) in W0`, and `eps = 0` gives `w in W cap K = 0`. So
  `S0 := phi S = W0 + v` is an `l`-space and `phi|_S` is an isomorphism onto
  it. Hence `F(S)|_W = F(W)` iff `F0(S0)|_(W0) = F0(W0)`, and
  `F(S)(u) = F0(S0)(v)`. The event "`v notin W0` and satisfied" is exactly
  the dimension-`d` event for `(W0, v)`. It depends only on `v`, and
  `F(S)(u)` also depends only on `v`.
* If `v in W0` and `u notin W`, then `S` contains a nonzero vector of `K`.
  The event may or may not be satisfied, and it adds a non-negative amount
  both to `val_W` and to the cost of every `psi`.

Since `v` is uniform, the first bullet gives `val_W >= val0_(W0)`. For the
cost, let `psi` be a functional on `F_2^n` and keep only the first bullet,
which can only lower the cost.

* If `psi` vanishes on `K`, then `psi = psibar o phi` for a functional
  `psibar` on `F_2^d`, and `psi(u) = psibar(v)`. The cost is the
  dimension-`d` cost of `psibar` at `W0`, which is at least `D0_(W0)`.
* If `psi` is nonzero on `K`, then `psi` is balanced on every coset of `K`.
  Given `v`, the event and `F0(S0)(v)` are fixed while `psi(u)` is a fair
  bit. So the cost is `(1/2) Pr_v[v notin W0, sat] = (1/2) s(W0)/4 = s(W0)/8`.
  By 1b, any `psibar notin C_(W0)` (there are `2^d - 4 > 0` of them) has
  `delta = x + psibar notin P` for every satisfied `nu`, so it pays exactly
  `(1/4)(s/2) = s/8` at dimension `d`. Hence `s(W0)/8 >= D0_(W0)`.

So `D_W >= D0_(W0)`.

**(5c) Uniformity of phi W.** Let `G_K <= GL_n` be the stabiliser of `K`.
It acts on `F_2^n / K`, which `phi` identifies with `F_2^d`, and the induced
map `G_K -> GL_d` is onto. To see this, fix a complement `U` with
`F_2^n = U + K`, and lift `A in GL_d` to the map that is
`(phi|_U)^(-1) A phi|_U` on `U` and the identity on `K`. The law of `W` is
`GL_n`-invariant, and the event "`W` meets `K` only in `0`" is
`G_K`-invariant. So the conditional law of `W` is `G_K`-invariant, and the
law of `phi W` is `GL_d`-invariant. Since `GL_d` is transitive on
`(l-1)`-spaces, `phi W` is uniform given injectivity. So
`E[val0_(phi W) | inj] = val(F0)` and `E[D0_(phi W) | inj] = D(F0)`.

**(5d) The probability p.** Build an ordered basis `w_1, ..., w_(l-1)` of
`W` one vector at a time. Step `i` (for `i = 0, ..., l-2`) has `2^n - 2^i`
choices. It has `2^n - 2^(i + n - d)` choices if also `w_(i+1)` must avoid
`span(w_1..w_i) + K`, and that condition over all steps is exactly
`W cap K = 0`. So

```text
p = prod_(i=0)^(l-2) (1 - 2^(i-l-1)) / (1 - 2^(i-n))
  >= 1 - sum_(i=0)^(l-2) 2^(i-l-1)  =  1 - (2^(l-1) - 1) 2^(-l-1)  >  3/4.
```

**(5e) Conclusion.** Combining 5a–5c,

```text
val(F) - 1/2  >=  (1-p)(1/2 - 2^(l-1-n)) + p (val(F0) - 1/2)  >=  p (val(F0) - 1/2),
D(F)          >=  p D(F0),
```

using `2^(l-1-n) <= 2^(-2) <= 1/2` for `n >= l+1`. If `F0` is a violator at
`gamma`, then `F` is a violator at `p gamma >= (3/4) gamma`. With Theorem B
this gives violators at `(3/4) gamma_B(l) >= (3/128) 2^(-l/2) >= 2^(-l/2)/43`
for every `n >= l+1` and `l >= 8`. At `n = l+1`, `K = 0`, `p = 1`, and `F = F0`.

## Checks

The artifact verifies each step by exact computation.

* Part A checks the dictionary of Step 1 against the primal definition.
* Part B checks the triangle cap of Step 2: exhaustively at `d = 3`, and by
  annealing at `d = 4..7`.
* Part C checks Step 4 by exact counts for `d = 4..20` and the closed-form inequality
  for `l = 4..199`.
* Part E checks Step 5 by primal brute force at
  `(n, l) = (4,2), (5,2), (5,3), (6,3)`. It confirms the formula for `p` and
  the equality lifted `gamma = p gamma0` in each case.

It exits 0 when run as
`python3 experiments/ugc-gstar-rainbow-2026-09-17/check_codim1_gstar_threshold.py`.
