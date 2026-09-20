---
rg: 2
id: hadamard-gadget-ratio-below-two-at-k6-proof
kind: route
title: Split the RM(1,6) spectrum into two RM(1,5) halves, sum exactly over the 48 AGL(5) classes of the first half with an AVX2 Gray code over the second, validate against the known k <= 5 values, and feed delta_6 < 16/47 into the decoded threshold adversary
target: hadamard-gadget-ratio-below-two-at-k6
requires:
  - hadamard-gadget-deletion-ratio-window
artifacts:
  - experiments/ugc-hadamard-k6-exact-2026-09-17/rm1_six_exact.c
  - experiments/ugc-hadamard-k6-exact-2026-09-17/k6_full_run.log
  - experiments/ugc-hadamard-k6-exact-2026-09-17/k5_validation.log
  - experiments/ugc-hadamard-k6-exact-2026-09-17/results-2026-09-19.txt
---

The notation is that of `hadamard-gadget-deletion-ratio-window`. Throughout,
`K = 2^k`, `xi in {-1,1}^(F_2^k)` is uniform, and
`W_i = sum_a xi_a (-1)^(a.i)`.

## Import

This comes from `hadamard-gadget-deletion-ratio-window`, item 3, which is
ESTABLISHED:

* `R*(k) <= 1 + delta_k (3 - 2^(2-k))`, with
  `delta_k = 1/2 - E max_i |W_i| / 2^(k+1)`;
* the same holds for `R*'(k)`, with
  `delta'_k = 1/2 - E max_i |W'_i| / (2(K - 1))` and `W'_i = W_i - xi_0`.

## Step 1: the half split

Take `k = n + 1` and write `a = (a', a_k)` and `i = (i', i_k)`, with
`a', i' in F_2^n`. Define

* `A_{i'} = sum_{a'} xi_{(a',0)} (-1)^(a'.i')`;
* `B_{i'} = sum_{a'} xi_{(a',1)} (-1)^(a'.i')`.

Then `W_{(i', i_k)} = A_{i'} + (-1)^(i_k) B_{i'}`. Since
`max(|u + v|, |u - v|) = |u| + |v|`,

    max_i |W_i| = max_{i'} (|A_{i'}| + |B_{i'}|).                    (1)

Write `f0, f1 : F_2^n -> F_2` for the sign patterns of the two halves, where
bit `a'` is set exactly when `xi = -1`. Put
`F(f0) = sum_{f1} max_{i'}(|A_{i'}| + |B_{i'}|)`. Then

    E max_i |W_i| = 2^(-2N) sum_{f0} F(f0),   with N = 2^n.

## Step 2: invariances of F

`F` depends on `f0` only through `|A|`. It is unchanged by each of the
following maps.

* **Linear substitution** `f0 -> f0 o M`, for `M in GL(n)`. Then
  `A_{i'} -> A_{M^{-T} i'}`. Substituting `f1 -> f1 o M`, which is a
  bijection of the `f1`, permutes `B` in the same way, and the max in (1)
  does not change.
* **Adding a linear function** `f0 -> f0 + <c, .>`. Then
  `A_{i'} -> A_{i' + c}`. The same substitution on `f1` shifts `B` the same
  way.
* **Adding the constant** `f0 -> f0 + 1`. Then `A -> -A`.
* **Translation** `f0 -> f0(. + b)`. Then `A_{i'} -> (-1)^(b.i') A_{i'}`, and
  `|A|` does not change.

So `F` is constant on each coset `f0 + RM(1,n)`. It is also constant on each
orbit of the affine substitution group acting on these cosets.

* **Coset sizes.** Every coset has exactly `2^(n+1)` elements.
* **Coset representatives.** `{0, e_1, ..., e_n}` is an information set of
  `RM(1,n)`. So each coset has a unique member that vanishes there, and the
  other `N - n - 1` bits index the coset.

## Step 3: the enumeration (`rm1_six_exact.c`, n = 5)

**Orbits.**

* The program runs a search over a bitmap of the `2^26` coset indices.
* Generators, each applied as `f -> canon(f o g)`: a cyclic shift of the
  variables, `x_1 <-> x_2`, `x_1 += x_2`, and `x_1 += 1`.
* Each generator is one of the maps in Step 2, so `F` is constant on every
  class the search finds.
* Correctness therefore needs only two facts, both checked at run time:
  * the classes partition the cosets, since their sizes sum to `2^26`
    exactly;
  * `canon` is idempotent and invariant under adding affine functions.
* It does not matter whether the generators give all of `AGL(5)`. They do,
  and the 48 classes found equal the Berlekamp–Welch count of affine classes
  of `RM(1,5)` cosets.

**Per-class sums.**

* For each representative, `F` is summed exactly over all `2^32` choices of
  `f1`.
* The complement `f1 -> f1 + 1` sends `B -> -B`. Each complementary pair has
  exactly one member with `f1(e_1 + ... + e_5) = 0`, meaning top bit `31`
  clear. So the program enumerates those `2^31` and doubles the sum.
* The enumeration is a Gray code. Flipping bit `p` changes `B` by
  `-+2 (-1)^(p.i')`.
* `B` is held in 32 `int8` lanes, with `|B_{i'}| <= 32` and
  `|A| + |B| <= 64 < 256`. The work is split into 16 jobs per class.
* Job sums are `uint64`, at most `2^27 * 64`. Totals are `unsigned __int128`.

**Total.**

* `T = sum_classes |class| F(rep)`.
* `E max|W| = 2^(n+1) T / 2^(2N) = T / (2^26 * 2^32)`.

**Output** (`k6_full_run.log`):

* `T = 6027415333417607360`;
* `E max|W| = T / 2^58 = 20.911797756684...`;
* `delta_6 = 1/2 - E/128 = 194052011567061629 / 2^59`.

## Step 4: validation

The same source with `n = 4` and `n = 3` (`k5_validation.log`) reproduces all
four of the following. Each was computed earlier by a different algorithm,
the info-set Gray code of `rm1_mean_distance.c`, and recorded in the window
node.

| value | reproduced |
|---|---|
| `delta_4` | `1961/8192` |
| `delta'_4` | `341/1536` |
| `delta_5` | `78015813/2^28`, with `T = 2 * 899230640`, twice the old coset sum |
| `delta'_5` | `2381339/2^23` |

The orbit counts are `3` and `8`, which match the known affine class counts
for `RM(1,3)` and `RM(1,4)`. The exact `k = 6` mean lies 1.2 standard errors
from the independent Monte Carlo estimate `20.9110 +- 0.0007`.

## Step 5: parity identity (proof of item 2)

Condition on `xi' = (xi_a)_{a != 0}`, and put `V_i = W'_i` and
`M = max_i |V_i|`.

* Each `V_i` is a sum of `K - 1` signs, so it is odd.
* Given `xi'`, the law of `xi_0` is uniform, so
  `E_{xi_0} max_i |V_i + xi_0| = (max_i |V_i + 1| + max_i |V_i - 1|) / 2`.
* If only `+M` is attained among the `V_i`, the two terms are `M + 1` and
  `M - 1`. The same holds if only `-M` is attained. In both cases the
  average is `M`.
* Suppose instead that both are attained, with `V_i = M` and `V_j = -M`.
  Then

      2M = V_i - V_j = 2 sum_{a . (i+j) = 1} xi_a (-1)^(a.i).

  The right-hand sum has `K/2` terms, an even number, so `M` would be even.
  This contradicts `M` being odd.
* So `E max|W| = E max|W'|` for every `k >= 2`. Substituting into the
  definitions gives `delta'_k = 1/2 - K(1 - 2 delta_k) / (2(K - 1))`.

The exact `k = 3, 4, 5` values above satisfy this identity.

## Step 6: conclusion

* `16/47 - delta_6 = 0.00379895... > 0`. As an exact comparison:
  `delta_6 * 47 < 16` holds, because
  `194052011567061629 * 47 = 9120444543651896563 < 16 * 2^59 = 9223372036854775808`.
* By the import, `R*(6) <= 1 + (47/16) delta_6`, which equals
  `18343816580506672371 / 2^63 = 1.98884057... < 2`.
* `delta'_6 = 1/2 - E / 126`, where `E = E max|W| = E max|W'|` by Step 5. This equals
  `27078344562813019 / 81064793292668928 = 0.3340333...`, giving
  `R*'(6) <= 1.9812230 < 2`.
