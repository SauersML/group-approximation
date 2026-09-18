---
rg: 2
id: black-box-repetition-sqrt-scale-proof
kind: route
title: Plug the odd cycle game with m about 1/2gamma into the universal bound and compare with the product-strategy round budget
target: black-box-repetition-needs-sqrt-scale-soundness-gap
requires: [raz-odd-cycle-repetition-lower-bound]
---

**Part 1.** Let `0 < gamma <= 1/8`, and let `m` be the largest odd integer
with `m <= 1/(2 gamma)`.

* Since `1/(2 gamma) >= 4`, we have `m >= 3`.
* We have `m > 1/(2 gamma) - 2 >= 1/(4 gamma)`, because `1/(4 gamma) >= 2`.
* The odd cycle game `C_m` is a unique game with
  `val(C_m) = 1 - 1/(2m) <= 1 - gamma`.

By the definition of a universal bound and by
`raz-odd-cycle-repetition-lower-bound`,

```text
F(gamma, n)  >=  val(C_m^(x n))  >=  1 - B sqrt(n)/m  >=  1 - 4 B gamma sqrt(n).
```

**Part 2.** Suppose a black-box amplifier exists with `eps' <= 1/2` and
`delta' < 1`. We bound the number of rounds `n`, then the soundness deficit
`gamma`.

The completeness condition is `(1-eta)^n >= 1 - eps'`. It gives
`n ln(1/(1-eta)) <= ln(1/(1-eps'))`. Two facts bound the logarithms:

* `ln(1/(1-eta)) >= eta`;
* `-ln(1-x) <= 2 ln(2) x <= 2x` on `[0,1/2]`, because `-ln(1-x)` is convex and
  therefore lies below its chord there.

So `n eta <= 2 eps'`, that is, `n <= 2 eps'/eta`.

Now consider the soundness deficit.

* **If `gamma > 1/8`,** the minimum in the statement is at most `1/8`, so the
  claim holds.
* **Otherwise,** Part 1 and the soundness condition give
  `delta' >= F(gamma, n) >= 1 - 4 B gamma sqrt(n)`. Hence
  `gamma >= (1 - delta')/(4 B sqrt(n))`. Using `n <= 2 eps'/eta`, this is
  `gamma >= (1 - delta') sqrt(eta)/(4 B sqrt(2 eps'))`. `square`

**Consequences.** Put `gamma = C sqrt(eta)`. Part 2 gives
`C >= (1 - delta')/(4 B sqrt(2 eps'))` whenever `gamma <= 1/8`.

Write `c = (1 - delta')/(4 B sqrt(2))`.

* If `gamma = L eta` with `L` fixed and `eta -> 0`, the bound needs
  `L sqrt(eta) >= c/sqrt(eps')`. This fails once
  `eta < c^2/(L^2 eps')`.
* If `gamma = o(sqrt(eta))`, the bound fails for every fixed `(eps', delta')`
  once `eta` is small.

The exact values `val(C_3) = 5/6` and `val(C_5) = 9/10` used to sanity-check
the odd cycle model are in `experiments/ugc-sqrt-scale-2026-09-17/output.txt`.
