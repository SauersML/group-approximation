---
rg: 2
id: fpbs-intrinsic-rates-log-lipschitz-in-parameter
kind: claim
title: The intrinsic-radius growth rates are log-Lipschitz in the percolation parameter, so they are continuous, vanish at p_c and satisfy lambda_1(t) <= log(t/p_c)
distinct_from:
  fpbs-intrinsic-l2-rate-closed-zero-set: that proves submultiplicativity in R, right-continuity and vanishing below p_c; its derivation of lambda_1(p_c) = 0 uses closedness of the zero set of an upper semicontinuous function, which does not follow. This claim supplies the missing left-side control by thinning shortest open paths, and gives the explicit bound log(t/p_c), which is sharp on trees
  fpbs-sphere-two-point-rate-right-continuous-universal: that is about extrinsic sphere sums of tau_p; here the rates are truncated by chemical distance, which is what lets a witness of length at most R be thinned at cost (t/q)^R
---

**ESTABLISHED.** Proof in `fpbs-intrinsic-rates-log-lipschitz-in-parameter-proof`.

**Setting.** As in `fpbs-intrinsic-l2-rate-closed-zero-set`: `G = Cay(Gamma,S)`
for a finitely generated nonamenable `Gamma`, `gr > 1` the growth rate,
`T^(R)_t(u,v) = P_t(d_omega(u,v) <= R)`, `a_R(t) = log||T^(R)_t||_(2->2)`,
`Lambda(t) = lim_R a_R(t)/R`, `lambda_1(t) = lim_R R^(-1) log E_t|B^int_R(o)|`,
and `p_Lambda = sup{t : Lambda(t) = 0}`, `p_lambda1 = sup{t : lambda_1(t) = 0}`.

**Theorem.** Let `0 < t <= q <= 1` and `R >= 1`.

1. *(Thinning.)* `T^(R)_q <= (q/t)^R T^(R)_t` entrywise, and
   `E_q|B^int_R(o)| <= (q/t)^R E_t|B^int_R(o)|`.
2. *(Log-Lipschitz.)* `Lambda(q) <= Lambda(t) + log(q/t)` and
   `lambda_1(q) <= lambda_1(t) + log(q/t)`. Together with monotonicity,
   `t -> Lambda(t)` and `t -> lambda_1(t)` are continuous on `[0,1]`.
3. *(Vanishing at criticality, repaired.)* `lambda_1(p_c) = Lambda(p_c) = 0`,
   and for every `t >= p_c`
   `Lambda(t) <= lambda_1(t) <= log(t/p_c)`.
   The zero sets are the closed intervals `[0,p_lambda1]` and `[0,p_Lambda]`,
   `p_c <= p_lambda1 <= p_Lambda`, and
   `Lambda(t) <= max(0, log(t/p_Lambda)) <= max(0, log(t/p_(2->2)))`.
4. *(Quantitative stretch divergence.)* If `K` is a linear stretch constant at
   `t` in the sense of item 4 of `fpbs-intrinsic-l2-rate-closed-zero-set`, then
   `t >= p_Lambda gr^(1/(2K)) >= p_c gr^(1/(2K))`. Equivalently, for
   `t > p_c`, `K_*(t) >= log(gr) / (2 log(t/p_c))`, which tends to infinity
   as `t ↓ p_c`.
5. *(Rate transfer to thresholds.)* If `Lambda(q) >= delta > 0`, then
   `q >= p_Lambda e^delta >= p_c e^delta`. The same holds for `lambda_1` with
   `p_lambda1`. In particular (IL2) `fpbs-intrinsic-l2-rate-bounded-below-above-pu`
   gives the quantitative gap `p_u >= p_c e^(Lambda(p_u))`, and (UCS) with
   constant `K` gives `p_u >= p_c gr^(1/(2K))`.

**Calibration.** On `T_d` the claim `fpbs-intrinsic-l2-rate-closed-zero-set`
records `lambda_1(t) = max(0, log(t(d-1)))` with `p_c = 1/(d-1)`, and
`Lambda(t) = max(0, log(t sqrt(d-1)))` with `p_Lambda = 1/sqrt(d-1)`. Both are
equality cases of item 3: `lambda_1(t) = log(t/p_c)` and
`Lambda(t) = log(t/p_Lambda)` above the respective thresholds. So the constant
`1` in front of `log(q/t)` cannot be improved in general. The tree is a check
only, and no step of the proof uses it.

**What this corrects.** In `fpbs-intrinsic-l2-rate-closed-zero-set-proof`,
Step 2 says the zero set `{Lambda <= 0}` "is closed by upper semicontinuity",
and Step 3 uses this to get `lambda_1(p_c) = 0`. An upper semicontinuous
function has closed *superlevel* sets `{f >= c}`, not closed sublevel sets.
Counterexample: `g_R(t) = min(1, max(1/R, 1 + R(t - p_c)))` are continuous and
nondecreasing, and `inf_R g_R = 1_[p_c,1]`, whose zero set `[0,p_c)` is not
closed. So items 3 (at `p_c` and at `p_c+`) and 6 of that claim, and the
closedness in its item 2, were not proved by that route. They are true, and
this claim proves them. Items 1, 4, the right-continuity in item 2, the
vanishing on `[0,p_c)` and `[0,p_(2->2))`, and item 5 in the form `q >= p_c`,
were proved there without the flawed step.

**What this does not give.** Item 3 bounds the rates from above near `p_c`.
A lower bound near `p_u` is still the OPEN chain (UCS) => (IL2) => (IL1).
Item 5 makes every rate lower bound at `p_u` quantitative, but it does not
supply one.
