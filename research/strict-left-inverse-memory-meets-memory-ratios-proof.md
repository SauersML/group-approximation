---
rg: 2
id: strict-left-inverse-memory-meets-memory-ratios-proof
kind: route
title: Vary the input on M alone; only the identity relay sees it, so the rule reads its first coordinate
target: strict-left-inverse-memory-meets-memory-ratios
requires: []
---

Suppose `S ∩ M M^-1 = {1}`. We show `tau` is surjective.

1. **The identity relay is private.** For `s` in `S` with `s != 1` and `m'` in `M`, the site
   `s m'` is not in `M`: otherwise `s = m m'^-1` lies in `M M^-1`.
2. **The decoder identity at the site 1.** For every configuration `x`,

       x(1) = sigma(tau(x))(1) = nu( ( mu( (x(s m))_(m in M) ) )_(s in S) ).

   The relay value at `s = 1` is `mu(x|_M)`. By step 1, the relay values at `s != 1` read `x`
   only at sites outside `M`.
3. **`mu` reads the label 1.** Fix `x` outside `M` and let `w` in `A^M` range over all
   assignments on `M`. The relay values at `s != 1` do not change, so
   `nu(mu(w), c) = w_1` for a fixed tuple `c`. Hence `mu(w) = mu(w')` implies `w_1 = w'_1`.
   The partition of `A^M` by the value of `mu` refines the partition by `w_1`. The latter has
   `|A|` blocks and the former at most `|A|`, so the two partitions coincide:
   `mu(w) = f(w_1)` for a permutation `f` of `A`.
4. **`tau` is surjective.** `tau(x)(g) = mu((x(g m))_m) = f(x(g))`, so `tau` is the bijection
   `x -> f o x`, with inverse `y -> f^-1 o y`.

So a non-surjective `tau` with a left inverse forces `S ∩ M M^-1 != {1}`.

**Rectangle form.** In a realization of strict data `D`, the forward cell `(s, m')` has value
`x_s x_m'` and the identity-row cell `(1, m)` has value `x_m`. A coincidence between them is
exactly `x_s = x_m x_m'^-1`. If the realized forward table has no such coincidence, steps 1–4
apply to the realized automata. They show `tau` is bijective, so `tau sigma = id`, which is
`Enc` at the realized reverse table. Every coarser reverse table then satisfies `Enc`, contradicting
strictness.

The argument uses no finite model, no property of `G` and no bound on the alphabet. No priority
is claimed: it is the row-1 step of Proposition 3 of the Boolean-core artifact, isolated.
