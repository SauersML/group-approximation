---
rg: 2
id: ug-hardness-deficit-ratio-padding-line-proof
kind: route
title: Count satisfied weight on the disjoint identity edge and on pointwise-distinct branches
target: ug-hardness-deficit-ratio-padding-line
requires: [unique-games-hard-at-completeness-one-half]
artifacts:
  - experiments/ugc-deficit-ratio-2026-09-17/check_deficit_ratio.py
---

Notation is as in the target claim. The premise is used only for the numbers
in item 3. Items 1, 2, 4 and 5 use nothing but the definitions (item 4 reads
the statement of `unique-games-conjecture` and does not use it as a premise).

**Item 1.** For `lambda = 0` put `P_0(U) = U`. Otherwise `p >= 1`, and the
identity edge has positive weight `pW`. The added vertices touch only the added
edge, so a labeling of `P_lambda(U)` is a labeling `x` of `U` together with
labels `(a, b)` on the new pair, and the two parts are independent. Giving the
new pair equal labels satisfies the identity edge. Hence

```text
val(P_lambda(U)) = (pW + (q - p) W val(U)) / (qW) = lambda + (1 - lambda) val(U).
```

The map `t -> lambda + (1 - lambda) t` is increasing, so YES instances go to
YES instances and NO instances to NO instances at the new thresholds. The map
is polynomial time and keeps the alphabet. Also
`1 - (lambda + (1-lambda) t) = (1 - lambda)(1 - t)`, so both deficits are
multiplied by `1 - lambda` and `R` is unchanged. As `lambda` ranges over
`[0, 1)`, the point runs along the segment to `(1, 1)`. `square`

**Item 2.** Since `1 - c > 0`, `R > 2` iff `1 - s > 2 - 2c` iff `s < 2c - 1`.
If `c <= 1/2`, then `2c - 1 <= 0 <= s`, so `R <= 2`. A point `(c, 2c - 1)` with
`1/2 <= c < 1` equals `(lambda + (1-lambda)/2, lambda)` for `lambda = 2c - 1`,
the padding of `(1/2, 0)`. `square`

**Item 3.** At `c = (1-eps)/2`, `s = eps`:
`R = (1 - eps) / ((1 + eps)/2) = 2(1-eps)/(1+eps)`, which is `< 2` for
`eps > 0`. By item 1 every padding has the same `R`, and by item 2 it lies
strictly above the line. `square`

**Item 4.** `unique-games-conjecture` asserts, for every `0 < eps < 1/2`, an
alphabet `K(eps)` with `Gap-UG_K[1 - eps, eps]` NP-hard. For `eps < 1/3` we
have `eps < 2(1 - eps) - 1 = 1 - 2 eps`, so the point is below the padding line,
and `R = (1 - eps)/eps -> infinity`. Taking `eps = 1/4` gives the NP-hard point
`(3/4, 1/4)` with `1/4 < 1/2 = 2c - 1`, which is the milestone
`unique-games-np-hard-below-the-padding-line`. `square`

**Item 5.** *Exactly one branch.* Let `e` be a proper constraint of arity `d_e`
between `x_i` and `x_j`, and fix labels `(a, b)`. The branches that hold are the
`t` with `pi_t(a) = b`. These are pairwise distinct values `pi_t(a)`, so at most
one branch holds. At least one holds iff `(a, b)` satisfies `e`.

*Split value.* For a labeling `x`, the satisfied weight of `Split(G)` is
`sum_e (w_e L / d_e) 1[x satisfies e]`, out of total `L W`. Thus

```text
val_x(Split(G)) = E_e 1[x satisfies e] / d_e,     E_e weighted by w_e / W,
```

and so `val(Split(G)) <= max_e 1/d_e <= 1/2`, or `<= 1/d` when every arity is
`d`.

*The kill.* Fix `n`, a YES input `x_Y` and a NO input `x_N` of length `n`, and
`lambda = lambda(n)`. By item 1,
`c <= val(Red(x_Y)) = lambda + (1 - lambda) val(Split(G_(x_Y))) <= lambda + (1 - lambda)/d`,
with `d = 2` in the mixed case. Also `s >= val(Red(x_N)) >= lambda`. Hence
`1 - s <= 1 - lambda` and `1 - c >= (1 - lambda)(1 - 1/d)`, so
`R(c, s) <= d/(d - 1)`, which is `<= 2`. By item 2 this is `s >= 2c - 1`.
No property of `Red` or `G_x` beyond the output form is used. `square`

**Check.** `experiments/ugc-deficit-ratio-2026-09-17/check_deficit_ratio.py`
brute-forces random small games. It checks the padding identity of item 1
and the split identity `val_x(Split(G)) = E_e 1[x satisfies e]/d_e` of item 5,
labeling by labeling, on proper linear 2-to-2 and 3-to-3 constraints over
`Z_m`. It is confirmation, not part of the proof.
