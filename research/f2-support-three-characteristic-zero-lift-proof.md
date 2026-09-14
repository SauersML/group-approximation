---
rg: 2
id: f2-support-three-characteristic-zero-lift-proof
kind: route
title: Solve the Kaplansky-graph edge equations with a character of the exponent-sum lattice
target: f2-support-three-zero-divisor-lifts-without-balanced-odd-cycle
requires: []
---

Write `A = {1, x, y}` and `S = AB`.

(1) **Two expressions.** For `s in G` the coefficient of `s` in
`alpha beta` is the number of `c in A` with `c^-1 s in B`, reduced mod 2.
That number is at most 3 and must be even, so it is `0` or `2`. If
`c b = c' b` then `c = c'`, so the two expressions of `s in S` have distinct
`b != b'`, and `K` has no loops (it may have parallel edges).

(2) **Letters.** If `s = c b = c' b'` then `b' = c'^-1 c b`. The six ordered
pairs `(c, c')` give the letters `u = c'^-1 c` shown below, and reversing the
edge replaces `u` by `u^-1`.

```text
(c, c'):  (1,x)  (x,1)  (1,y)  (y,1)  (x,y)    (y,x)
u:        X^-1   X      Y^-1   Y      Y^-1 X   X^-1 Y
```

(3) **Edge equations.** Fix `s, t in k^*` and put `r_1 = 1`, `r_x = s`,
`r_y = t`. Let `psi: F(X, Y) -> k^*` be the homomorphism with `psi(X) = s`,
`psi(Y) = t`. A function `w: B -> k^*` makes the coefficient of `s in S` in
`(1 + s x + t y) sum_b w(b) b` vanish exactly when
`r_c w(b) + r_(c') w(b') = 0`, that is `w(b') = theta w(b)` with
`theta = -r_c / r_(c')`. Checking the six pairs of (2),
`theta = -psi(u)`: for example `(x, y)` gives `-s/t = -psi(Y^-1 X)`. Points
outside `S` receive no terms. So a solution `w` gives the zero divisor.

(4) **Cycle condition.** Propagating `w` from one base vertex per component
along a spanning forest of `K` defines `w` uniquely; it satisfies every edge
equation if and only if every closed walk `gamma` satisfies
`prod theta = (-1)^(L(gamma)) psi(w_gamma) = 1`, where `w_gamma` is the word
read. Since `psi(w_gamma) = s^(e_X) t^(e_Y)` with `e(gamma) = (e_X, e_Y)`, the
condition is

```text
s^(e_X(gamma)) t^(e_Y(gamma)) = (-1)^(L(gamma))   for all closed walks gamma.
```

(5) **Linearity.** Each edge contributes a fixed vector `e(u) in Z^2` and
length `1`; reversal negates `e(u)` and keeps the parity of the length. So
`gamma -> e(gamma)` and `gamma -> L(gamma) mod 2` induce homomorphisms
`e: H_1(K; Z) -> Z^2` and `pi: H_1(K; Z) -> Z/2`. It suffices to impose (4)
on `H_1(K; Z)`.

(6) **A character.** By hypothesis `pi` vanishes on `ker e`, so `pi` induces a
homomorphism `bar pi: Lambda = e(H_1(K)) -> {+1, -1}`. Choose a basis
`f_1, f_2` of `Z^2` with `Lambda = Z d_1 f_1 + Z d_2 f_2` (Smith normal
form, `d_i >= 0`). In `k^*` with `k` algebraically closed of characteristic
`!= 2`, choose `z_i` with `z_i^(d_i) = bar pi(d_i f_i)` when `d_i > 0`, and
`z_i = 1` otherwise. The homomorphism `chi: Z^2 -> k^*` with
`chi(f_i) = z_i` restricts to `bar pi` on `Lambda`. Put
`s = chi(1, 0)`, `t = chi(0, 1)`. Then `s^(e_X) t^(e_Y) = chi(e(gamma)) =
(-1)^(L(gamma))` for all `gamma`, which is (4).

(7) **Conclusion.** By (4) the propagated `w` is well defined with values in
`k^*`, and by (3) `(1 + s x + t y) sum_b w(b) b = 0`. Both factors are nonzero
with supports `{1, x, y}` and `B`.

(8) **Corollary.** If `k[G]` has no zero divisors, the hypothesis of (6)
fails, so some `z in H_1(K; Z)` has `e(z) = 0` and `pi(z) = 1`. In a
bipartite graph every closed walk has even length, so `pi = 0` on
`H_1(K; Z)`; hence `K` is not bipartite. When `K` is connected, `pi_1(K)`
surjects onto `H_1(K; Z)`, and `e`, `pi` are functions of the class, so `z` is
represented by a closed walk with zero exponent sums and odd length.

(9) **Check.** `G = Z/3 = <g>`, `x = g`, `y = g^2`, `B = {1, g}`. The points
`1, g, g^2` each have two expressions, giving three edges between `1` and `g`
with letters `Y^-1`, `X`, `X^-1 Y` read from `1` to `g`. `H_1(K)` has basis
the walks reading `X^-1 Y^-1` and `Y^-1 X X` (lengths 2), so
`Lambda = <(-1,-1), (2,-1)>` and `pi = 0`; solving gives `t = s^-1`,
`s^3 = 1`.
