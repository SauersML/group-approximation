---
rg: 2
id: cv-coset-refinements-are-edge-label-coset-systems-proof
kind: route
title: A support fixpoint and one Goursat quotient per pair turn a refinement into shared edge labels, and padding splits off as a matrix tensor factor
target: cv-coset-refinements-are-edge-label-coset-systems
requires: []
---

Notation as in the target.  `R` has PVMs `p_q` over `K_q`, with

```text
p_q^s p_(q')^(s') = 0   whenever (s,s') is not in R_e = c_e D_e,   e = {q,q'}.   (CS)
```

**(P1) Support fixpoint.**  Start with `S_q = K_q` for every `q`.  Repeatedly
choose a pair `e = {q,q'}` and replace `S_q` by the first projection of
`R_e ∩ (S_q x S_(q'))`.
- **Cosets are preserved.**  An intersection of left cosets is empty or a left
  coset, and a projection of a left coset is a left coset.  So every `S_q` stays
  a coset.
- **The algebra is unchanged.**  If `s` is removed, no `s'` in `S_(q')` is a
  partner of `s`.  So, inductively, `p_q^s = sum_(s' in S_(q')) p_q^s p_(q')^(s') = 0`.
- **The fixpoint.**  The process stops.  If some `S_q` is empty then
  `1 = sum_s p_q^s = 0`.  Otherwise, at the fixpoint,
  `R'_e = R_e ∩ (S_q x S_(q'))` projects onto both `S_q` and `S_(q')`.

This is the support fixpoint of part 5 of the artifact
`research/artifacts/ex-kac-quantum-compiler-relabeling-collapse-2026-09-13.md`.

**(P2) Edge labels.**  Write `S_q = s_q K~_q`.
- Then `R'_e = (s_q a, s_(q') a') D'_e` for some `D'_e <= K~_q x K~_(q')` that
  projects onto both factors.
- **Goursat.**  There are `N ⊴ K~_q`, `N' ⊴ K~_(q')` and an isomorphism
  `theta : K~_q/N -> K~_(q')/N'` with `D'_e = {(k,k') : theta(kN) = k'N'}`.
- **Labels.**  Put `L_e = K~_q/N`, and

  ```text
  ell_e(s_q k) = (a^(-1)N)(kN),      ell'_e(s_(q') k') = theta^(-1)((a'^(-1)N')(k'N')).
  ```

- **Properties.**  Both maps are left translates of surjective homomorphisms
  onto `L_e`, and `(s,s') in R'_e` iff `ell_e(s) = ell'_e(s')`.

**(P3) Block sums are shared.**  For `lambda in L_e` put
`F_e^lambda = sum_(s in S_q, ell_e(s) = lambda) p_q^s`.
- **Sharing.**  Insert `1 = sum_(s') p_(q')^(s')` and delete the terms killed by
  (CS).  This gives

  ```text
  F_e^lambda = sum_(ell_e(s) = lambda = ell'_e(s')) p_q^s p_(q')^(s'),
  ```

  and the same computation from the other side gives the same sum.  So `F_e^lambda`
  is a function of `p_q` and also a function of `p_(q')`.
- **Conversely**, if the block sums agree and each `p_q` vanishes off `S_q`, then
  (CS) holds.  For `ell_e(s) != ell'_e(s')`,
  `p_q^s p_(q')^(s') = p_q^s F_e^(ell_e(s)) F_e^(ell'_e(s')) p_(q')^(s') = 0`.

**(P4) The system `N(R)`.**
- `Phi_q = (ell_e)_(e ∋ q) : S_q -> prod_(e ∋ q) L_e` is a left translate of a
  homomorphism.  So `T_q = Phi_q(S_q)` is a left coset.
- The `F_e` with `e ∋ q` are functions of `p_q`, so they commute.  Their joint
  spectral measure is the pushforward of `p_q` along `Phi_q`, which lives on
  `T_q`.
- So `ell_e |-> F_e` defines a unital *-homomorphism `A(N(R)) -> A(R)`.

**(P5) Lifting representations.**  Let PVMs `ell_e` in `M` satisfy the relations
of `N(R)`.  For `tau in T_q` put `p_q^tau = prod_(e ∋ q) ell_e^(tau_e)`.
- **The matrix factor.**  The fibres of `Phi_q` are cosets of its kernel, of
  common size `n_q`.  Put `n = lcm(n_q)`, and for each `q` choose in `M_n` a
  diagonal PVM `(e^q_i)_(i <= n_q)` whose projections each have rank `n/n_q`.
- **The lift.**  Number each fibre by `i(s)`.  Put
  `p_q^s = p_q^(Phi_q(s)) (x) e^q_(i(s))` for `s in S_q`, and `p_q^s = 0` off `S_q`.
- **Checks.**
  - These are PVMs, and their block sums are `ell_e (x) 1` from both sides.  So
    (CS) holds by (P3).
  - The trace `tau (x) tr_n`, embeddability into `R^U` and finite dimensionality
    all pass to the lift.
  - The pushforwards of context answers and variable answers are unchanged.

This proves (NF1).

**(P6) Readouts.**  Let `e = (c,v)` be an incidence.
- **Definition.**  Every block of `R'_e` lies in the preimage of the accepting
  set.  So `beta_c(s)_v = beta_v(s')` whenever `ell_e(s) = ell'_e(s') = lambda`.
  Call this common value `psi_e(lambda)`.
- **At contexts.**  For `s in S_c`, `beta_c(s) = psi(Phi_c(s))`, which lies in
  `Allowed_c`.
- **At variables.**  For `t in S_v`, `psi_e(ell'_e(t)) = beta_v(t)` for every
  `e ∋ v`.
- **The variable.**  `X_v = sum_t (-1)^(beta_v(t)) p_v^t = sum_lambda (-1)^(psi_e(lambda)) F_e^lambda`.

This proves (NF2).

**(P7) Converse.**  Given `N` satisfying (NF2), write `T_q = g_q H_q`.
- **The refinement.**  Put `K_q = H_q`, `beta_c(h) = psi(g_c h)`,
  `beta_v(h) = psi_e((g_v h)_e)` for any `e ∋ v`, and
  `R_e = {(h,h') : (g_q h)_e = (g_(q') h')_e}`.
- **`R_e` is a coset.**  With the coordinate homomorphisms `rho, rho'`, `R_e` has
  the form `{(h,h') : rho(h) = b rho'(h')}`.  It is nonempty by hypothesis.
  - For `(h_0,h'_0) in R_e`, membership is equivalent to
    `rho(h_0^(-1) h) = rho'(h'_0^(-1) h')`.
  - So `R_e` is the left coset `(h_0,h'_0) D_0`, where
    `D_0 = {(h,h') : rho(h) = rho'(h')}`.
- **Acceptance.**  `R_e` is accepted on every incidence by (NF2).
- **The isomorphism.**  `p_q^h |-> prod_e ell_e^((g_q h)_e)` and `ell_e |-> F_e`
  are inverse unital *-homomorphisms.  The first is well defined because
  `H_q -> prod_(e ∋ q) L_e` is injective.
