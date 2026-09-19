---
rg: 2
id: fpbs-layer-renewal-along-homomorphism-is-critical-l2
kind: claim
title: BK layer renewal along a homomorphism to Z never closes above p_c with scalar coefficients, and closes with operator coefficients only by proving p_c < p_(2->2)
distinct_from:
  fpbs-orbit-uniform-half-tilt-bounds-connectivity-operator: that kills boundary-cocycle tilts whose half-tilted sum is bounded uniformly on an orbit; this kills first-visit renewal in the height of a homomorphism to Z, whose coefficients are band sums or band operator norms, with no tilt and no boundary.
  fpbs-co-amenable-subgroup-relative-threshold-is-pc: that proves chi^I_p = infinity above p_c for co-amenable I; this uses it for I = ker h to show that every scalar band coefficient, under every submultiplicative weight, is infinite above p_c.
  fpbs-central-amenable-relative-threshold-is-pu: that shows RG along amenable subgroups of groups with infinite centre is exactly BS; this shows that on every group with infinite abelianization the renewal proof of RG along a cyclic subgroup of nonzero height is at least as hard as p_c < p_(2->2).
  fpbs-relative-gap-along-every-amenable-subgroup-universal: that is the OPEN universal RG; this kills one class of proofs of its cyclic instances and does not decide RG.
artifacts:
  - research/fpbs-layer-renewal-along-homomorphism-is-critical-l2-proof.md
---

**ESTABLISHED (class kill).** Proof route:
`fpbs-layer-renewal-along-homomorphism-is-critical-l2-proof`.

**Setting.**
- `Gamma` is finitely generated and nonamenable. `S` is a finite symmetric
  generating set. `G = Cay(Gamma,S)` has edges `{x, xs}`, and `o = 1`.
- `h : Gamma -> Z` is a surjective homomorphism, `K = max_(s in S) |h(s)|`,
  and `N = ker h`.
- The **relative band** `j >= 0` of a pair `(x,y)` is
  `h(y) - h(x) in [jK, (j+1)K)`. The absolute band is
  `Lambda_j = h^(-1)[jK, (j+1)K)`.
- `R_j(x,y) = tau_p(x,y) 1{(x,y) in relative band j}`. This is a
  `Gamma`-invariant nonnegative kernel, and `r_j = ||R_j||_(2->2)`.
- A **weight** is `w : Gamma -> (0, infinity)` with `w(xy) <= w(x) w(y)`.
  Examples are `1`, `e^(lambda h)` and `e^(lambda |x|_S)`. The weighted
  band sum is `beta^w_j = sum_(x in Lambda_j) tau_p(o,x) w(x)`.

**Theorem.** Let `p in (0,1)`.

1. **Renewal (BK at the first band visit).** For `i, j >= 1`, entrywise
   `R_(i+j) <= R_j (R_(i-1) + R_i)`. Hence `r_(i+j) <= r_j (r_(i-1) + r_i)`
   and `beta^w_(i+j) <= beta^w_j (beta^w_(i-1) + beta^w_i)`.
2. **Scalar coefficients are infinite.** If `p > p_c(G)`, then
   `beta^w_j = infinity` for every weight `w` and every `j in Z`.
3. **Operator coefficients are critical l2.** Suppose `r_(J-1) + r_J < 1`
   for some `J >= 1`. Then:
   - every `r_j` is finite, and `r_n` decays exponentially in `n`;
   - `||T_p||_(2->2) <= 2 sum_(j>=0) r_j < infinity`, so `p <= p_(2->2)`.

   Conversely, `sup_j r_j <= ||T_p||` always holds.
4. **Kill.** Take any proof of exponential decay of `tau_p(o,z^n)` with
   `h(z) != 0`, or of `E_p|K_o ∩ <z>| < infinity`, at some `p > p_c`, that
   closes the renewal inequality of item 1 with a finite coefficient below
   `1`. Every such proof falls into one of two cases:
   - (a) the coefficient is a scalar band sum. Then it dies at the step
     "coefficient finite", by item 2;
   - (b) the coefficient is a band operator norm. Then it proves
     `p_c < p_(2->2)`, by item 3. That is the critical `l^2` gap, which is
     at least as strong as `p_c < p_u` on `G`.

**Named invariant.** The scalar case uses two facts:
- `ker h` is co-amenable, because `Gamma/ker h = Z`;
- every weight satisfies the symmetrization bound
  `w(x) + w(x^(-1)) >= 2 sqrt(w(1)) >= 2`.

Because of these, the degree-zero band already carries a relative
susceptibility equal to `chi^N_p = infinity`. No choice of `K`, band width,
`J` or weight avoids this.

**Calibration.** On `T_4 = Cay(F_2,{a,b}^(±1))` with `h(a) = 1` and
`h(b) = 0`:
- the target is true, since `tau_p(o,a^n) = p^n`;
- the operator route works for `p < 1/sqrt 3 = p_(2->2)` (Haagerup
  inequality);
- every scalar band sum is infinite for `p > 1/3 = p_c`.

So the obstruction lies in the method, not in the target.

**Scope.** The kill applies to every group with infinite abelianization, and
to every Cayley graph of it. Examples:
- `Lambda x Z` for every generating set (the class of Choi–Seo Q1.3);
- `F_n x F_m`, braid groups, RAAGs and surface groups.

It leaves open renewals whose coefficient is restricted to a half-space,
`beta^hs_j = sum_(z in Lambda_j) P_p(o <-> z inside {h < jK} ∪ {z})`. On
`T_4` a heuristic count says they are also infinite above `p_c`:
first-passage words have growth rate `3`, with only a polynomial ballot
correction. This count is not proved here. In general their
divergence above `p_c` is a half-space form of Grimmett–Marstrand, which is
not proved here.

## Attempts
