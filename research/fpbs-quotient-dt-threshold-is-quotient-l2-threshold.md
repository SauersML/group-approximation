---
rg: 2
id: fpbs-quotient-dt-threshold-is-quotient-l2-threshold
kind: claim
title: For a normal subgroup the quotient spectral DT threshold equals the quotient l2 threshold, so critical fibre l2 holds iff some pushed-forward critical ball boundary measure has norm below one
distinct_from:
  fpbs-spectral-dt-threshold-equals-l2-threshold: that is the case N = {1}, proved by the sphere tail bootstrap; this treats every normal N, where the Gamma-sphere does not map to the complement of a Q-ball and the bootstrap does not apply, and uses thinning instead.
  fpbs-quotient-spectral-dt-certificates-are-subgroup-blind: that proves a relative certificate gives finite chi^H_p and is never easier than the absolute one; this proves the converse direction for normal N, that every p below p^Q_(2->2)(N;G) has a relative certificate, and the operator (not only diagonal) bound.
  fpbs-sphere-fibre-operator-iff-critical-fibre-l2: that characterises critical fibre l2 by a sphere-restricted operator built from the full two-point function; this characterises it by finitely supported measures on Q whose coefficients are polynomials in p.
  fpbs-relative-threshold-is-quotient-l2-threshold: that is the open Claim E, p_c(N;G) = p^Q_(2->2)(N;G); this proves nothing about p_c(N;G), it gives a finite-volume form of the right-hand side.
---

**ESTABLISHED** (proof: `fpbs-quotient-dt-threshold-is-quotient-l2-threshold-proof`).

**Setting.** `G = Cay(Gamma, D)`, `N` a normal subgroup, `Q = Gamma/N`,
`pi : Gamma -> Q`. For finite `S` containing `o`,

```text
nu_{S,p}(g) = p * sum_{ {u,v} in Delta S, v = g } P_p(o <->_S u),
sigma^N_p(q) = sum_{x in q} tau_p(o,x),
p^Q = p^Q_(2->2)(N;G) = sup{p : ||sigma^N_p||_Q < infinity}.
```

`pi_* nu` is a finitely supported measure on `Q`, and `||.||_Q`, `sp_Q` are
the norm and spectral radius of convolution on `l2(Q)`. Note
`rho_Q(pi_* nu) = rho_{N\Gamma}(nu)`, the Schreier operator of the
blindness node.

1. **Certificate bound.** If `sp_Q(pi_* nu_{S,p}) < 1`, then entrywise
   `sigma^N_p <= sum_{k>=0} (pi_* nu_{S,p})^{*k} * pi_* 1_S`, and so
   `||sigma^N_p||_Q <= |S| sum_k ||rho_Q(pi_* nu_{S,p})^k|| < infinity`.
2. **Every p below p^Q certifies.** If `p < p^Q`, then
   `||rho_Q(pi_* nu_{B_R,p})|| -> 0` as `R -> infinity`.
3. **Thresholds.** `p^Q_sDT(N;G) = p^Q_(2->2)(N;G)`, where
   `p^Q_sDT = sup{p : some finite S has sp_Q(pi_* nu_{S,p}) < 1}`.
4. **Finite-volume form of critical fibre l2.** The following are equivalent:
   * `||sigma^N_(p_c)||_Q < infinity` (alternative (i) of C1 in
     `fpbs-relative-threshold-is-quotient-l2-threshold`);
   * `p_c < p^Q_(2->2)(N;G)`;
   * some finite `S` has `sp_Q(pi_* nu_{S,p_c}) < 1`;
   * some ball has `||rho_Q(pi_* nu_{B_R,p_c})|| < 1`.
5. **Kesten normal gap, finite-volume form.** Under the weak form `E'(G,N)`,
   `p_c < p_c(N;G)` holds iff some critical ball boundary measure, pushed to
   `Q`, has `l2(Q)` convolution norm below one. At `N = {1}` this is item 3
   of `fpbs-spectral-dt-threshold-equals-l2-threshold`.

**What it does not do.** By blindness, `sp_Gamma(nu) <= sp_Q(pi_* nu)`, so a
quotient certificate is at least as hard as an absolute one. Item 4 therefore
gives no new route to `p_c < p_(2->2)`. It turns C1(i), and with it every proof
of the Kesten premise under `E'`, into a check on one explicit family of
finitely supported measures on `Q`, with coefficients polynomial in `p`.
