---
rg: 2
id: f2-set-spectral-laws-obey-quotient-collision-and-harper-bounds
kind: claim
title: The spectral law nu_S = N hat(1_S)^2 / |S| of any S in F_2^k obeys nu(W) <= min(1, |W| |S| / N) on dual subspaces and the Harper quotient bound 2 sum_i nu{chi.b_i = 1} >= log2 1/nu(B^perp) for every independent b_1..b_r with span B
distinct_from:
  f2-cayley-subgroup-sets-lose-at-most-log-inverse-density: that uses only the subspace mass bound (M) and loses log(1/delta); this adds the Harper quotient inequality (H), which is exactly the constraint the order-c mass-only extremal law violates.
  f2-cayley-subgroup-sets-are-constant-factor-optimal: that is the dominance conjecture itself; this is a pair of necessary conditions on spectral laws, used by route f2-cayley-dominance-from-bounded-mass-harper-relaxation.
  mass-only-spectral-relaxation-of-subgroup-dominance-is-order-c: that shows (M) alone cannot bound the dominance constant; this proves the extra inequality (H) that kills its witness.
artifacts:
  - research/f2-set-spectral-laws-quotient-bounds-proof.md
  - experiments/f2-cayley-dominance-2026-09-17/spectral_relaxation.py
---

**Statement.** Let `N = 2^k`, `S` a nonempty subset of `F_2^k` with `|S| = s`,
`f = 1_S`, `f^(chi) = N^(-1) sum_x f(x) (-1)^(chi.x)`, and
`nu(chi) = N f^(chi)^2 / s`, a probability law on characters (Parseval) with
`nu(0) = s/N`. Put `d_S(a) = |S \ (S+a)|/s = 2 nu{chi : chi.a = 1}`.

- **(M) quotient collision bound.** For every subspace `W` of the character
  space, `nu(W) <= min(1, |W| s / N)`.
- **(H) Harper quotient bound.** For every linearly independent
  `b_1, ..., b_r` in `F_2^k` with span `B` and `B^perp = {chi : chi.b = 0 for all b in B}`,

```text
sum_(i<=r) d_S(b_i)  =  2 sum_(i<=r) nu{chi : chi.b_i = 1}  >=  log2( 1 / nu(B^perp) ).
```

With `B = F_2^k` and `s = 2^(k-c)` this is `sum_i d_S(b_i) >= c` for every
basis, the edge-isoperimetric fact behind `C = 1` for independent generators.
The proof (self-contained, including Harper's inequality) is the route
`f2-set-spectral-laws-quotient-bounds-proof`. `spectral_relaxation.py check`
replays both on random sets at `(k, c) = (5, 2), (6, 3)` (0 violations).

**Role.** (M) is all that the stopping-time proof of the log loss uses, and
`mass-only-spectral-relaxation-of-subgroup-dominance-is-order-c` shows that
(M) alone forces a factor of order `c`. (H) is violated by that extremal law, so
(M)+(H) is the next relaxation to test
(`f2-cayley-mass-harper-spectral-relaxation-is-bounded`).
