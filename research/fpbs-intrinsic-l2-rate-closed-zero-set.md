---
rg: 2
id: fpbs-intrinsic-l2-rate-closed-zero-set
kind: claim
title: The exponential l2 growth rate of intrinsic-radius connection kernels is right-continuous, vanishes on [0,p_c] and is at least log gr over twice any linear chemical stretch constant
distinct_from:
  fpbs-nonamenability-bounds-critical-connectivity-operator: that is Hutchcroft's critical l2 conjecture, boundedness of the full kernel T_(p_c); here only the exponential rate of the intrinsic-radius truncations is controlled, and it vanishes at p_c on every nonamenable Cayley graph with no critical input beyond sharpness
  fpbs-bk-majorant-integrated-sensitivity-is-critical-l2: that integrates the Russo-BK inequality in the parameter p; here BK is used in the intrinsic radius R at fixed p, giving submultiplicativity in R and hence semicontinuity in p, and no parameter integration occurs
  fpbs-sphere-two-point-rate-below-arccosh-universal: that is about exponential rates of extrinsic sphere sums of tau_(p_c); here the kernel is truncated by chemical distance, which is what makes the rate submultiplicative in the radius and right-continuous in p
  fpbs-universal-subcritical-pivotal-growth-rate: that is about near-critical pivotal growth rates; this rate involves no pivotals and is defined and semicontinuous on the whole interval [0,1]
---

**ESTABLISHED.** Proof in `fpbs-intrinsic-l2-rate-closed-zero-set-proof`.

**Setting.** `Gamma` is finitely generated and nonamenable, `S` is a finite
symmetric generating set, `G = Cay(Gamma,S)` with edges `{g,gs}`, `o` is the
identity, `|B_m|` is the ball cardinality and `gr = lim_m |B_m|^(1/m) > 1`.
`omega_t` is Bernoulli(`t`) bond percolation in the standard monotone coupling,
`d_omega` is chemical (intrinsic) distance, `+infinity` between different
clusters. For an integer `R >= 1` define the **intrinsic-radius kernel**

```text
T^(R)_t(u,v) = P_t( d_omega(u,v) <= R ),
a_R(t)       = log || T^(R)_t ||_(2->2),
Lambda(t)    = lim_R a_R(t)/R,
lambda_1(t)  = lim_R (1/R) log E_t |B^int_R(o)|,
```

where `B^int_R(o) = {v : d_omega(o,v) <= R}`.

**Theorem.**

1. *(BK submultiplicativity.)* `T^(R+R')_t <= T^(R)_t T^(R')_t` entrywise.
   Hence `a_(R+R') <= a_R + a_(R')`, and the analogous inequality holds for
   `log E_t|B^int_R(o)|`. Both limits exist and equal the infimum over `R`,
   with `0 <= Lambda(t) <= lambda_1(t) <= log d`.
2. *(Semicontinuity.)* For each `R`, `t -> a_R(t)` is continuous and
   nondecreasing. Hence `Lambda` and `lambda_1` are nondecreasing, upper
   semicontinuous and right-continuous on `[0,1]`. Their zero sets are closed
   intervals `[0,p_Lambda]` and `[0,p_lambda1]`.
3. *(Vanishing at criticality.)* `Lambda = lambda_1 = 0` on `[0,p_c]`, so
   `p_c <= p_lambda1 <= p_Lambda`. Also `lambda_1(t) -> 0` and
   `Lambda(t) -> 0` as `t` decreases to `p_c`. More generally
   `||T_t||_(2->2) < infinity` implies `Lambda(t) = 0`, so
   `p_(2->2) <= p_Lambda`.
4. *(Stretch lower bound.)* Say `K` is a **linear stretch constant at `t`** if
   `inf_(u,v) P_t(d_omega(u,v) <= K(d(u,v)+1)) > 0`. Write `K_*(t)` for the
   infimum of such `K`, and `+infinity` if there are none. If `K` is a linear
   stretch constant at `t`, then `Lambda(t) >= log(gr)/(2K)`. `K_*` is
   nonincreasing in `t`.
5. *(Contradiction lemma.)* If there are `q < 1`, `epsilon > 0` and
   `delta > 0` with `Lambda(t) >= delta` for all `t in (q, q+epsilon)`, then
   `Lambda(q) >= delta` and `q > p_Lambda >= p_c`. The same holds with
   `lambda_1` and `p_lambda1` in place of `Lambda` and `p_Lambda`. Since
   `lambda_1 = inf_R R^(-1) log E|B^int_R(o)|`, `lambda_1(q) >= delta` is
   equivalent to `E_q|B^int_R(o)| >= e^(delta R)` for **every** `R >= 1`.
6. *(Divergence of stretch at `p_c+`.)*
   `K_*(t) >= log(gr) / (2 lambda_1(t))`, so `K_*(t) -> infinity` as `t`
   decreases to `p_c`, on every nonamenable Cayley graph.

**Calibration.** On the `d`-regular tree `T_d` (`gr = d-1`, `p_c = 1/(d-1)`,
`p_u = 1`), the path to `v` is unique. So `T^(R)_t(o,v) = t^|v| 1_(|v|<=R)`, and
the radial computation for `T_d` (Haagerup-type estimate
`||sum_(|g|=n) lambda(g)|| ~ (n+1)(d-1)^(n/2)` for free groups) gives
`Lambda(t) = max(0, log(t sqrt(d-1)))`. Indeed `p_Lambda = 1/sqrt(d-1)`, which
equals `p_(2->2)` there, and `lambda_1(t) = max(0, log(t(d-1)))` with
`p_lambda1 = p_c`. The tree computation is a check on the statement, and no
step of the proof uses it.

**What this does not give.** Item 3 is universal because `lambda_1`
dominates `Lambda` and vanishes below `p_c` by sharpness. It says nothing about
`||T_(p_c)||`. Item 5 turns any uniform lower bound on `Lambda` just above `p_u`
into `p_c < p_u`. That lower bound is the OPEN claim
`fpbs-intrinsic-l2-rate-bounded-below-above-pu`.
