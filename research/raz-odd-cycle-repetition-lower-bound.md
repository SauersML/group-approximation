---
rg: 2
id: raz-odd-cycle-repetition-lower-bound
kind: claim
title: The odd cycle unique game of size m has value 1-1/2m and n-fold repeated value at least 1-(1/m)O(sqrt n) (Raz 2008)
distinct_from:
  dinur-steurer-projection-game-repetition-bound: that is an upper bound on repeated values of projection games; this is Raz's matching lower bound for one explicit unique game.
---

**ESTABLISHED, BY CITATION.** For odd `m >= 3` let `C_m` be the odd cycle game.
Alice gets `x` uniform in `Z_m`. Bob gets `y = x` with probability `1/2` and
`y = x +- 1` with probability `1/4` each. The answers are bits; they must be
equal when `x = y` and different otherwise. `C_m` is a unique game on alphabet
`{0,1}` with `val(C_m) = 1 - 1/(2m)`. Raz shows that there is an absolute
constant `B` with

```text
val(C_m^(x n))  >=  1 - B sqrt(n) / m        for all odd m >= 3 and all n >= 1.
```

So Rao's and Dinur--Steurer's `(1 - eps^2)^Omega(n)` behaviour for unique games
is tight. No universal bound of the form `val(G) <= 1 - gamma =>
val(G^(x n)) <= F(gamma, n)` can beat `1 - O(gamma sqrt n)`
(`black-box-repetition-needs-sqrt-scale-soundness-gap`).

The values `val(C_3) = 5/6` and `val(C_5) = 9/10` are checked exactly in
`experiments/ugc-sqrt-scale-2026-09-17/output.txt` (check [5]).

This is not a new result.

DERIVATION raz-odd-cycle-repetition-citation
