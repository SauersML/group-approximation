---
rg: 2
id: fpbs-tree-projected-branch-share-last-crossing-bound
kind: claim
title: Branch shares over a free quotient are bounded by products of half-graph branching factors
distinct_from:
  fpbs-hyperbolic-quotient-far-halfspace-share: that is the open premise that far-halfspace shares vanish uniformly below p_c for every group with a hyperbolic quotient; this is an inequality valid at every p for generating sets projecting into a free basis, which reduces that premise there to a branching factor below one.
---

Let `pi : Gamma -> F_n` be a surjection, `B` a free basis of `F_n`, and `S` a
finite symmetric generating set of `Gamma` with `pi(S) ⊆ {1} ∪ B ∪ B^(-1)`.
Write:
* `X = Cay(Gamma,S)`, `o` the identity, `Gamma_q = pi^(-1)(q)`;
* `beta(w)` for the set of reduced words beginning with the reduced word `w`;
* `m_s = #{g in S : pi(g) = s}` for a letter `s`, so `m_(s^(-1)) = m_s`.

For a letter `s` let `X^(s)` be the subgraph of `X` induced on
`pi^(-1)(F_n \ beta(s^(-1)))`, the half graph missing the branch in direction
`s^(-1)`. Put

```text
chi^H_p      = E_p|K_o ∩ Gamma_1|,
chi^(s)_p    = E_p|K^(X^(s))_o ∩ Gamma_1|,
lambda_p(s)  = p m_s chi^(s)_p,
sigma_p(s)   = E_p|K_o ∩ Gamma_s|.
```

Then for every `p in [0,1]` and every reduced word `w = s_1 ... s_D`, `D >= 1`:

1. `E_p|K_o ∩ pi^(-1) beta(w)| <= chi^H_p · p m_(s_D) · prod_(j<D) lambda_p(s_j) · chi_p`.
2. `sigma_p(s) <= chi^H_p lambda_p(s)` and `lambda_p(s^(-1)) <= m_s sigma_p(s)` for
   every letter `s`.
3. If `sup_(p<p_c) chi^H_p < infinity` and `sup_(p<p_c) max_s lambda_p(s) < 1`,
   then the far-halfspace share of `X` tends to zero. That is premise (ii) of
   `fpbs-hyperbolic-quotient-fibre-estimates-l2-gap`, for any rough similarity of
   the tree `F_n` into hyperbolic space.
4. **Fibre sums and sphere bubbles.**
   `sigma_p(w) = E_p|K_o ∩ Gamma_w| <= chi^H_p prod_(j<=D) lambda_p(s_j)`.
   Hence the fibre-sphere bubble `b_R(p) = sum_(|w|=R) sigma_p(w)^2` obeys

   ```text
   b_R(p) <= (chi^H_p)^2 · 1^T N_p^(R-1) v_p,
   N_p(s,t) = lambda_p(t)^2 1{t != s^(-1)},   v_p(s) = lambda_p(s)^2.
   ```

   So `b_R(p_c) -> 0` geometrically when `chi^H_(p_c) < infinity` and the
   non-backtracking matrix `N_(p_c)` has spectral radius below one, e.g. when
   `(2n-1) max_s lambda_(p_c)(s)^2 < 1`. Here `p_c`-values are left limits,
   which exist by monotonicity.

**Scope.** It applies to every tree-projected generating set of `F_n x Z`,
e.g. `{(a,0),(a,1),(b,0),(1,1)}`, and more generally to any group mapping onto
`F_n`, with any kernel.

**Relation to the first-hit bound.** Section 4.3 of
`research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md`
bounds the branch share by `(max_s sigma_p(s))^D`, using first hits of the
fibres. Last crossings remove one within-fibre spreading factor per step. By
item 2 the two sufficient conditions are ordered when every `m_s = 1`: then
`max_s sigma_p(s) < 1` gives `max_s lambda_p(s) < 1`, and it also bounds
`chi^H_p <= sigma_p(s)/p`. With some `m_s >= 2` they are not comparable in
general.

Proof: `fpbs-tree-projected-branch-share-last-crossing-proof`.
