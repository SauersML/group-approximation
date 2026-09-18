---
rg: 2
id: tfd-unbounded-irreps-group-is-not-strictly-hs-stable-proof
kind: route
title: Compress an irreducible by one dimension, then the (T;FD) gap on the intertwiner space forbids same-dimension rounding
target: tfd-unbounded-irreps-group-is-not-strictly-hs-stable
requires: []
---

Self-contained. Notation: `sigma: Gamma -> U(k+1)` is irreducible, `xi` is a
unit vector, and `iota: C^k -> C^(k+1)` is an isometry onto `xi^perp`, so
`1 - iota iota^* = xi xi^*`.  On `Hom(C^k, C^(k+1))` use
`<X, Y> = tr_k(Y^* X)` with `tr_k = Tr/k`.  Left multiplication by a unitary
of `C^(k+1)` and right multiplication by a unitary of `C^k` preserve this
norm, and `||iota||_2 = 1`.  A rank-`<= 1` operator of operator norm `<= 1`
has normalized norm `<= 1/sqrt(k)`.

**Step 1 (polar compression).**  For `s in S` put `A_s = iota^* sigma(s) iota`,
a contraction on `C^k`.  Then

```text
1 - A_s^* A_s = iota^* sigma(s)^* xi xi^* sigma(s) iota,
```

which is positive, of rank `<= 1` and of norm `<= 1`.  Let `A_s = V_s |A_s|`
be a polar decomposition with `V_s` unitary, and set `tau(s) = V_s`.  Since
`1 - x <= 1 - x^2` for `0 <= x <= 1`, the operator `1 - |A_s|` is positive,
of rank `<= 1` and of norm `<= 1`, so

```text
||A_s - V_s||_2 = ||V_s(|A_s| - 1)||_2 <= 1/sqrt(k).
```

Also `sigma(s) iota - iota A_s = xi xi^* sigma(s) iota` has rank `<= 1` and
norm `<= 1`.  Hence

```text
||sigma(s) iota - iota tau(s)||_2 <= 2/sqrt(k).                    (P1)
```

Words use `tau(s^(-1)) = tau(s)^*`.  Multiplying the operator in (P1) on
the left by `sigma(s)^*` and on the right by `tau(s)^*` gives
`iota tau(s)^* - sigma(s)^* iota`, so the same bound holds for `s^(-1)`.

**Step 2 (words and relators).**  For a word `w = x_1 ... x_n` over
`S^(+-1)`, telescoping gives

```text
sigma(w) iota - iota tau(w)
  = sum_j sigma(x_1...x_(j-1)) (sigma(x_j) iota - iota tau(x_j)) tau(x_(j+1)...x_n),
```

so `||sigma(w) iota - iota tau(w)||_2 <= 2n/sqrt(k)`.  If `r in R`, then
`sigma(r) = 1`, and since `iota` is an isometry,
`||tau(r) - 1||_2 = ||iota - iota tau(r)||_2 <= 2|r|/sqrt(k)`.  This is (TU1).

**Step 3 (no invariant intertwiner).**  Let `rho: Gamma -> U(k)` be any
exact representation.  Then `pi(g) X = sigma(g) X rho(g)^(-1)` is a unitary
representation of `Gamma` on the finite-dimensional Hilbert space
`H = Hom(C^k, C^(k+1))`.  If `pi(g) theta = theta` for all `g`, then
`sigma(g) theta = theta rho(g)`.  So `theta(C^k)` is a `sigma`-invariant
subspace of dimension `<= k < k+1`, and irreducibility forces
`theta(C^k) = 0`.  Hence `H^Gamma = 0` and every vector of `H` is orthogonal
to the invariants.

**Step 4 (the gap).**  Put `delta = max_(s in S) ||tau(s) - rho(s)||_2`.  For
`s in S`,

```text
||pi(s) iota - iota||_2 = ||sigma(s) iota - iota rho(s)||_2
                       <= ||sigma(s) iota - iota tau(s)||_2 + ||tau(s) - rho(s)||_2
                       <= 2/sqrt(k) + delta,
```

and `||pi(s^(-1)) iota - iota||_2 = ||iota - pi(s) iota||_2`.  For `g` of
word length `<= m`, telescoping in the unitary representation `pi` gives
`||pi(g) iota - iota||_2 <= m (2/sqrt(k) + delta)`.  By (T;FD) applied to
`pi` and `v = iota`, where `||iota||_2 = 1` and `iota` is orthogonal to
`H^Gamma = 0`,

```text
kappa_0 <= max_(g in S_0) ||pi(g) iota - iota||_2 <= m (2/sqrt(k) + delta),
```

so `delta >= kappa_0/m - 2/sqrt(k)`.  This is (TU2).

**Corollary.**  Choose irreducible `sigma_n` of dimensions `k_n + 1 -> infinity`.
The tuples `tau_n` have defect `<= 2L/sqrt(k_n) -> 0`.  For `k_n > 16/kappa^2`
their distance to every exact `k_n`-dimensional representation is
`>= kappa/2`.  So for `eps = kappa/2` no `delta > 0` satisfies the
same-dimension stability condition. ∎

**Where one extra dimension repairs it.**  `sigma` itself, on `C^(k+1)`, is
at distance `O(k^(-1/2))` from the padded tuple `tau (+) 1` on generators, by
(P1).  So the obstruction is exactly the codimension-one defect, in line with
`tfd-low-leakage-compressions-flexibly-reduce`.  The theorem is silent on
flexible stability.

