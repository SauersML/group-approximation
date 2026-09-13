---
rg: 2
id: hs-invisible-corona-maps-full-trace-padding-proof
kind: route
title: Cut the joint defect square function diagonally, then compress the remainder
target: hs-invisible-corona-maps-are-full-trace-paddings
requires:
  - matrix-corona-projection-monoid-is-rank-germs
  - op-to-hs-shadow-residual-functoriality
---

Enumerate `G = {g_1, g_2, ...}` and choose unitary lifts `U_n(g)`.

**(a) implies (b).** Put

```text
D_n^(k) = sum_(j <= k) 2^(-j) (U_n(g_j) - 1)^* (U_n(g_j) - 1) >= 0.
```

By (a), `tr D_n^(k) -> 0` for every fixed `k`. Choose `N_1 < N_2 < ...` with
`tr D_n^(k) <= 1/k^2` for `n >= N_k`. For `N_k <= n < N_(k+1)` put `k(n) = k`
and `e_n = 1_([0,1/k])(D_n^(k))`; for `n < N_1` put `e_n = 1`. Then

```text
tr(1 - e_n) <= k(n) tr D_n^(k(n)) <= 1/k(n) -> 0,
```

and for `xi in Ran e_n` and `j <= k(n)`,

```text
||(U_n(g_j) - 1) xi||^2 <= 2^j <D_n^(k(n)) xi, xi> <= 2^j ||xi||^2 / k(n).
```

So for each fixed `j`, `||(U_n(g_j) - 1) e_n|| -> 0`. The class `p` of `(e_n)`
is a projection with `rho(g_j) p = p` for all `j`, and
`tau_omega(1 - p) = lim tr(1 - e_n) = 0`.

**(b) implies (a).** `tau_omega(rho(g)) = tau_omega(p) + tau_omega(rho(g)(1-p))`.
The first term is `1`. By the Cauchy--Schwarz inequality for the trace,
`|tau_omega(rho(g)(1-p))| <= ||rho(g)|| tau_omega(1-p) = 0`.

**Part 1.** Applying `rho(g^(-1)) p = p` and taking adjoints gives
`p rho(g) = p`. So `p` commutes with `rho(g)`, and
`rho(g) = p rho(g) p + (1-p) rho(g) (1-p) = p + (1-p) rho(g) (1-p)`.

**Part 2.** By `matrix-corona-projection-monoid-is-rank-germs`, `1 - p` has a
projection lift `q_n` of eventually well-defined rank `s_n`, and
`s_n/d_n = tr q_n -> 0` because every ultralimit of `tr q_n` vanishes. Since
`q_n` is a lift, `(1-p) Q_d (1-p)` is the corona of the corners
`q_n M_(d_n) q_n ~= M_(s_n)`, indexed by `n in J`. By Part 1 the remainder is
multiplicative, and `rho(g) = 1` iff `(1-p) rho(g) (1-p) = 1 - p`.

**Part 3.** Corona homomorphisms and operator-norm asymptotic
representations determine each other through unitary lifts. So
`R_(infinity->2)(G) = G` says exactly that every corona homomorphism
satisfies (a), hence (b). The remainder `rho'` is a corona homomorphism on
`J`, so it again satisfies (a) in its own normalized trace.

**Part 4.** A nontrivial finite-dimensional unitary representation `pi` is a
constant operator-norm asymptotic representation with `||pi(g) - 1||_2 > 0`
for some `g`, so `g` is outside the shadow residual.

Now let `rho` be a corona homomorphism, `p` as in (b), `e_n = 1 - q_n`.
Suppose the set in part 4 is infinite for some `g`, `c` and `C`. Since
`rho(h) p = p = p rho(h)`, we have `(U_n(h) - 1) e_n -> 0` and
`e_n (U_n(h) - 1) -> 0` for every fixed `h`, so `[q_n, U_n(h)] -> 0` and

```text
||q_n (U_n(g) - 1) q_n|| >= ||U_n(g) - 1|| - o(1) >= c - o(1)
```

along the set. Pass to an infinite subset on which `s_n = s` is constant,
identify `Ran q_n` with `C^s`, and put `T_n(h) = q_n U_n(h) q_n`. These are
asymptotically unitary and asymptotically multiplicative for fixed `h`.
Compactness of the unit ball of `M_s`, along a free ultrafilter on that
subset, gives an exact unitary representation `pi : G -> U(s)` with
`||pi(g) - 1|| >= c`. That contradicts the first sentence of this part.
