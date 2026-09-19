---
rg: 2
id: fpbs-orbit-uniform-half-tilt-bounds-connectivity-operator
kind: claim
title: The pointwise half-tilted susceptibility is a Schur test function, so a bound uniform along one boundary orbit bounds the connectivity operator on l2, and an L2 bound over the boundary makes the two-point function square summable
distinct_from:
  fpbs-boundary-tilted-susceptibility-kernel: that proves the tilt framework and the implication from the nu-averaged half tilt to (K); this studies the pointwise functional X_p(zeta) before averaging and shows its sup along an orbit dominates ||T_p||_(2->2) and its L2(nu) norm dominates ||tau_p(o,.)||_2
  fpbs-boundary-half-tilt-above-pc-universal: that is the open L1(nu) statement [BT]; this proves that the L-infinity and L2 versions of [BT] are at least as strong as p_c < p_(2->2) and p_c < p_2 respectively, which kills orbit-uniform routes to [BT]
  fpbs-nonamenability-bounds-critical-connectivity-operator: that is the open critical l2 conjecture; this shows an orbit-uniform half tilt at any p >= p_c implies it, so it gives no route to it
  fpbs-two-point-lq-threshold-gap-universal: that asks tau_p(o,.) in l^q for q > 2; this shows the L2(nu) half tilt forces the q = 2 case and is not a route to q > 2
---

**ESTABLISHED.** Proof in `fpbs-orbit-uniform-half-tilt-bounds-connectivity-operator-proof`.

**Setting.** The notation is that of `fpbs-boundary-tilted-susceptibility-kernel`:
`G = Cay(Gamma,S)`, `d = |S|`, `(Z,nu)` a quasi-invariant probability
`Gamma`-space, `Delta_zeta(x,y) = (d nu_y/d nu_x)(zeta)`. Define the
**pointwise half-tilted susceptibility**

```text
X_p(zeta) = sum_y tau_p(o,y) Delta_zeta(o,y)^(1/2)   in [0,infinity],
```

so that `chi^nu_(1/2)(p) = int X_p d nu` by Tonelli. Write `T_p` for the
operator with kernel `tau_p` on `l2(Gamma)`, `p_(2->2)` for its threshold, and
`p_2 = sup{p : sum_y tau_p(o,y)^2 < infinity}`.

**Theorem.** There is a `Gamma`-invariant `nu`-conull set `W` such that the
following hold.

1. **(Schur identity.)** For `zeta in W` put `psi_zeta(y) = Delta_zeta(o,y)^(1/2)`.
   Then `psi_zeta > 0` and, for every `x`,
   `(T_p psi_zeta)(x) = psi_zeta(x) X_p(x^(-1) zeta)`.
2. **(Orbit bound.)** For every `zeta in W` and `p in [0,1]`,
   `||T_p||_(2->2) <= sup_(g in Gamma) X_p(g zeta)`.
   In particular `||T_p||_(2->2) <= ess sup_nu X_p`.
3. **(L2 gradation.)** `int X_p^2 d nu >= sum_y tau_p(o,y)^2`.
4. **(Consequences for the ladder of half tilts.)** Put
   `p^(nu,r)_t = sup{p : X_p in L^r(nu)}` for `r in [1,infinity]`, so that
   `p^(nu,1)_t = p^nu_t`. Then

   ```text
   p^(nu,infinity)_t <= p_(2->2) <= p_2,    p^(nu,2)_t <= p_2,
   p^(nu,infinity)_t <= p^(nu,2)_t <= p^nu_t .
   ```

   Hence, on every nonamenable Cayley graph:
   - if `X_p` is essentially bounded for some `p >= p_c`, or bounded along a
     single orbit of a point of `W`, then `||T_(p_c)|| < infinity`, so
     `p_c < p_(2->2)` and `p_c < p_u`;
   - if `X_p in L2(nu)` for some `p > p_c`, then `p_c < p_2 <= p_u`;
   - if `p >= p_(2->2)`, then `X_p` is unbounded on every orbit in `W`.
5. **(Radial majorants cannot certify L2.)** Let `f >= 0` be a function of
   the word length. If `sum_y f(|y|) psi_zeta(y)` is in `L2(nu)`, then
   `sum_k f(k)^2 |S_k| < infinity`, where `S_k` is the sphere of radius `k`.
   For `f(k) = gr^(-k/2)`, with `gr` the growth rate of `G`, the series
   diverges. So the pointwise majorant `tau_(p_c)(o,y) <= gr^(-|y|/2)` cannot
   certify `X_(p_c) in L2(nu)` for any `nu`.
6. **(Openness of the uniform threshold.)** Suppose
   `D = max_(s in S) ess sup_zeta Delta_zeta(o,s) < infinity`, and
   `sup_W X_(p_0) = M < infinity` for some `p_0`. Then for `0 <= q - p_0 < 1/(d D^(1/2) M)`,

   ```text
   sup_W X_q <= M / (1 - d D^(1/2) M (q - p_0)) .
   ```

   So `{p : sup_W X_p < infinity}` is an interval that is open on the right
   when `D < infinity`.

**What it changes for [BT].** Item 4 names the invariant that kills every
orbit-uniform route to `fpbs-boundary-half-tilt-above-pc-universal`:
`sup_(g) X_p(g zeta) >= ||T_p||_(2->2)`. See Attempt 2 there.
