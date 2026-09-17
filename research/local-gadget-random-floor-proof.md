---
rg: 2
id: local-gadget-random-floor-proof
kind: route
title: Pin the best auxiliary assignment of one satisfying tuple and move one primary at a time, so each one-primary part is a row minimum paid by random labels
target: local-gadgets-above-exactness-pay-a-random-assignment-floor
requires: []
artifacts:
  - experiments/edge-local-gadget-floor-2026-09-17/check_gadget_floor.py
---

Notation is as in the target claim. Fix one patch `N` with `k` primaries, and
drop the subscript `N`.

## Decomposition

Fix an auxiliary assignment `A`. Every constraint of the gadget falls in exactly
one of three classes, according to how many primaries its scope meets.

* **No primary.** Its satisfaction depends on `A` only. Write `c_A >= 0` for the
  satisfied weight of this class.
* **Exactly one primary `z`.** Given `A`, its satisfaction depends on `x_z` only.
  Write `f_(A,z)(t) >= 0` for the satisfied weight of this class when `x_z = t`.
* **Two or more primaries.** By the restriction on scopes, these are direct
  constraints. Their satisfaction depends on `x` only. Write `h(x)`.

So the value of `(x, A)` is `c_A + sum_z f_(A,z)(x_z) + h(x)`, and
`v(x) = h(x) + max_A (c_A + sum_z f_(A,z)(x_z))`.

## Item 1 (local inequality)

Let `A*` attain the maximum at `x`. Take any `x'` with `x'_z = x_z`. Then

```text
v(x') >= c_(A*) + sum_(z') f_(A*,z')(x'_(z')) + h(x') >= c_(A*) + f_(A*,z)(x_z),
```

because every term is nonnegative. Minimizing over `x'` gives
`r_z(x_z) >= c_(A*) + f_(A*,z)(x_z)`. Sum over the `k >= 1` primaries and use
`c_(A*) >= 0`:

```text
sum_z r_z(x_z) >= k c_(A*) + sum_z f_(A*,z)(x_z) >= c_(A*) + sum_z f_(A*,z)(x_z) = v(x) - h(x).
```

## Item 2 (patch floor)

Average item 1 over `x ~ S`:

```text
c - ex = E_S [v - h] <= sum_z E_S r_z(x_z) = sum_z sum_t Pr_S[x_z = t] r_z(t)
       <= sum_z (M / K_z) sum_t r_z(t) = M sum_z E_(t uniform) r_z(t).
```

This uses `r_z >= 0`. Pointwise `r_z(x_z) <= v(x)`, so
`E_(t uniform) r_z(t) = E_(x uniform) r_z(x_z) <= E_(x uniform) v(x) = floor`.
Hence `c - ex <= M k floor`.

## Item 3 (instance floor)

The auxiliaries are private to their patch. So for a fixed primary labeling `x`
the output value is `sum_N mu_N v_N(x_N)`, and `val(Gamma(Phi))` is its maximum
over `x`. Draw `x` uniformly and independently at each outer vertex. The
primaries of a patch are distinct vertices, so `x_N` is uniform on
`prod_(z in N) [K_z]`. Therefore

```text
val(Gamma(Phi)) >= E_x sum_N mu_N v_N(x_N) = sum_N mu_N floor_N,
```

and item 2 bounds each `floor_N` from below. Nothing about `Phi` other than the
patch data is used, so this holds on NO instances.

## Item 4 (direct exactness)

Write `h = sum_j w_j 1[(x_L, x_R) in pi_j]` with `pi_j` partial permutations,
`sum_j w_j = W`. Then `E_S 1[pi_j] = |pi_j cap S| / |S| <= min(K_L, K_R) / |S|`.
Biregularity gives `|S| = K_L d_L = K_R d_R`, so this is
`min(1/d_L, 1/d_R) = 1/max(d_L, d_R)`. Summing, `ex <= W/d <= 1/d`. A 2-to-2
constraint has `d_L = d_R = 2`, and a 2-to-1 constraint `[2n] -> [n]` has
`d_L = 1`, `d_R = 2`. Both give `1/2`.

## Item 5 (reduction trade-off)

Take a NO instance `Phi`. By hypothesis `sum_N mu_N c_N >= c` for its gadget
family. The output is a unique game, so every direct constraint is a
permutation of weight at most `1`, and item 4 gives `ex_N <= 1/2`. With `k = 2`
and `M = 1`, items 2 and 3 give

```text
s >= val(Gamma(Phi)) >= sum_N mu_N (c_N - ex_N)/2 >= (c - 1/2)/2,
```

which is `c <= 1/2 + 2s`.

A remark on scope. The hypothesis is the only place where YES and NO inputs
meet. It holds for every reduction whose completeness proof reads "if the outer
labels of `N` lie in `S_N`, the gadget reaches value at least `alpha_N`" with the
gadget depending only on the shape of `S_N`, because then `c_N >= alpha_N` on
all inputs. The hypothesis is not automatic. A gadget built from global data
of `Phi` (for example, from a relaxation solution) may reach high value only on
the planted tuples of a YES instance and not on average over `S_N`. Such a
reduction certifies completeness through global structure, not patch by patch,
and lies outside this claim except for the sub-relation form covered in the
target claim.

## Item 6 (tightness)

* **Split.** `S` is the union of the blocks `{2i, 2i+1}^2` on `[K]`, and the
  direct constraints are `id` and `x -> x xor 1`, each of weight `1/2`. Every
  pair in `S` satisfies exactly one, so `c = ex = 1/2`. Off `S` neither holds, so
  `floor = |S| / (2 K^2) = 1/K`.
* **Block projection.** There is one auxiliary `u` with alphabet `[K/2]`, with the
  constraints `u = floor(x/2)` and `u = floor(y/2)` of weight `1/2` each. Pairs in
  `S` satisfy both, so `c = 1`. Off `S` one is satisfiable, so
  `floor = (|S| + (K^2 - |S|)/2) / K^2 = 1/2 + 1/K`. Item 2 reads
  `1 <= 1 + 2/K`.

The replay `check_gadget_floor.py` (seed `20260917`, 3000 trials, output in
`run-output.txt`) evaluates `v` and `h` by exhaustive enumeration. It checks
items 1, 2 and 4 on random unique and arbitrary-predicate gadgets over 2-to-2,
3-to-3 and 2-to-1 relations and random 3-vertex patches, and it replays both
tightness examples in exact arithmetic.
