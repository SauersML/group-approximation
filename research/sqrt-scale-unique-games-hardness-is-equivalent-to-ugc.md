---
rg: 2
id: sqrt-scale-unique-games-hardness-is-equivalent-to-ugc
kind: claim
title: UGC holds iff for every C some Gap-UG_k[1-eta, 1-C sqrt(eta)] with eta <= 1/C^2 is NP-hard, with an explicit squaring law
distinct_from:
  rich-2to1-conjecture-is-equivalent-to-ugc: that is the Braverman--Khot--Minzer equivalence with Rich 2-to-1 games, a different constraint class; this is an equivalence inside unique games that moves the soundness threshold from near 0 to 1 - C sqrt(eta).
  small-set-expansion-hypothesis-implies-ugc: that is a one-way implication from expansion hardness; this is a two-way equivalence obtained by parallel repetition.
  unique-games-hard-at-completeness-one-half: that is an unconditional gap at completeness 1/2; this is a conditional equivalence at completeness near 1.
---

**ESTABLISHED.** Let `Gap-UG_k[c, s]` be as in
`sqrt-scale-unique-games-hardness`. The following are equivalent:

```text
(UGC)   for every eps in (0,1/2) there is k with Gap-UG_k[1-eps, eps] NP-hard;
(SQ)    for every C >= 1 there are eta in (0,1/C^2] and k with
        Gap-UG_k[1-eta, 1-C sqrt(eta)] NP-hard.
```

**Amplification with explicit constants.** Suppose `Gap-UG_k[1-eta, 1-g]` is
NP-hard, and let `eps', delta'` be in `(0, 1/2]`. Suppose further that
`g^2 >= 32 ln(1/delta') eta/eps'` and `eta <= eps'`. Then
`Gap-UG_(k^t)[1-eps', delta']` is NP-hard for `t = floor(eps'/eta)`.

**Squaring law.** Suppose `Gap-UG_k[1-eta_0, 1-R sqrt(eta_0)]` is NP-hard,
with `R >= 6` and `eta_0 <= 1/R^2`. Then:

* `Gap-UG_(k^t)[1 - 17/R^2, 1/e]` is NP-hard for `t = ceil(16/(R^2 eta_0))`;
* for every rational `rho` in `(0,1]`,
  `Gap-UG_(k^t)[1 - 17 rho/R^2, 1 - (1-1/e) rho]` is NP-hard.

So at every scale `eta = 17 rho/R^2` the linear deficit ratio
`(1-1/e) R^2/17 >= R^2/27` is NP-hard.

Proof in `ugc-sqrt-scale-equivalence-proof`. Numerics for all parameter
choices are in `experiments/ugc-sqrt-scale-2026-09-17/output.txt`, checks [2]
and [3].

**How much of this is new.** The equivalence is a folklore consequence of
Rao's and Dinur--Steurer's repetition bounds, and Raz's paper frames the
question of strong repetition in these terms. New here are three things:

* the in-graph statement with explicit constants;
* the squaring law, which connects to a linear deficit ratio;
* the pairing with the two sharpness facts. One is
  `black-box-repetition-needs-sqrt-scale-soundness-gap`: the sqrt scale is
  forced, and `C ~ eps'^-1/2` is necessary. The other is
  `sqrt-scale-ug-hardness-costs-alphabet-exp-c-squared`: ratio `C` needs
  `log k >~ C^2`.

**What it changes.** The root's gap `1-eps` versus `eps` can be replaced, with
no loss, by a gap in which both values are near `1`:

* completeness `1 - eta`;
* soundness `1 - C sqrt(eta)`.

A reduction attacking UGC may stop at any constant soundness deficit ratio `C`
at the sqrt scale, as long as `C` is unbounded over the family.
Conversely, a family of algorithms reaching `1 - C_0 sqrt(eta)` uniformly in `k`
would refute UGC.

DERIVATION ugc-sqrt-scale-equivalence-proof
