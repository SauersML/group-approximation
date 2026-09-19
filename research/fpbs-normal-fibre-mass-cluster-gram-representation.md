---
rg: 2
id: fpbs-normal-fibre-mass-cluster-gram-representation
kind: claim
title: For every normal subgroup the fibre mass is a cluster-averaged Gram function, so it is maximal at the identity and positive definite, and its operator is bounded by the squared Kesten norm of the cluster profile
distinct_from:
  fpbs-amenable-normal-fibre-mass-maximal-at-subgroup: that proves sigma_p(q) <= sigma_p(1) and positive definiteness only for amenable normal H, by Følner pairing; this proves maximality for every normal N and every p, and positive definiteness for every normal N whenever clusters are finite, by mass transport. It settles open point 1 of that artifact.
  fpbs-normal-fibre-second-moment-maximal: that bounds the second fibre moment, E Y_q^2 <= E X^2, so its corollary is sup_q sigma_p(q) <= (E X^2)^(1/2); this bounds the first moment directly, sup_q sigma_p(q) = chi^N_p, and needs no relative sharpness.
  fpbs-fibre-summed-connectivity-operator: that compares ||T_p|| with ||lambda_Q(sigma_p)||; this writes lambda_Q(sigma_p) itself as an average of Gram operators R_a^* R_a over the cluster profile a, which gives a new upper bound on it.
  fpbs-quotient-l2-threshold-sandwich: that orders the thresholds and gives the lower bound chi^N_p <= ||sigma_p||_Q; this gives the upper bound ||sigma_p||_Q <= E_p[ ||lambda_Q(a)||^2 / |K_o| ].
artifacts:
  - research/artifacts/fpbs-cluster-gram-fibre-operator-2026-09-17.md
---

**ESTABLISHED.** The proof is in
`fpbs-normal-fibre-mass-cluster-gram-representation-proof`.

**Setting.**

- `Gamma` is finitely generated and `S` is a finite symmetric generating set.
  Bernoulli(`p`) bond percolation runs on `Cay(Gamma,S)`.
- `N` is any normal subgroup, amenable or not, `Q = Gamma/N`, and `u~` is any
  lift of `u in Q`.
- For a vertex `x` the **cluster profile** is
  `a_x(u) = |K_x ∩ x u~ N|`, which does not depend on the lift. Write `a = a_o`.
- The fibre mass is `sigma_p(u) = E_p a(u)`, and `chi^N_p = sigma_p(e)`.

**Theorem.**

1. **(First-moment maximality, every `p`, every normal `N`.)** For all `u in Q`,

   ```text
   sigma_p(u) = sigma_p(u^{-1}) <= sigma_p(e) = chi^N_p.
   ```

   More precisely, if `chi^N_p < infinity` then `a(u) < infinity` a.s., and

   ```text
   sigma_p(u)^2 <= E[ a(e) 1{a(u) >= 1} ] * E[ a(e) 1{a(u^{-1}) >= 1} ].
   ```

2. **(Gram representation.)** Suppose `|K_o| < infinity` a.s., which holds for
   every `p < p_c(G)`. Then for every `u in Q`,

   ```text
   sigma_p(u) = E_p[ |K_o|^{-1} sum_{v in Q} a(v) a(vu) ],
   ```

   and for every finitely supported `f : Q -> C`,

   ```text
   sum_{u,w} conj(f(u)) f(w) sigma_p(u^{-1} w)
       = E_p[ |K_o|^{-1} sum_{v in Q} | sum_u a(vu) f(u) |^2 ]  >= 0.
   ```

3. **(Positive definiteness.)** `sigma_p` is a positive definite function on `Q`
   for every `p < p_c(G)`. The same holds at `p = p_c(G)` whenever
   `chi^N_(p_c) < infinity`.

4. **(Gram norm bound.)** Let `||.||_Q` be the norm of the sandwich node
   `fpbs-quotient-l2-threshold-sandwich`, and put
   `r(a) = ||lambda_Q(a)|| / ||a||_1`, the Kesten ratio of the profile. It lies in
   `(0,1]`. For every `p < p_c(G)`,

   ```text
   chi^N_p  <=  ||sigma_p||_Q  <=  E_p[ ||lambda_Q(a)||^2 / |K_o| ]
                                =  E_p[ |K_o| r(a)^2 ]  <=  chi_p,
   ```

   and at criticality

   ```text
   ||sigma_(p_c)||_Q  <=  liminf_{p ↑ p_c}  E_p[ |K_o| r(a)^2 ].
   ```

**Consequences.**

- **Uniform fibre bounds for every normal subgroup.** The fibre-bubble bounds of
  Corollary E in `research/artifacts/fpbs-amenable-normal-fibre-mass-bound-2026-09-16.md`
  now hold for every normal `N`:
  `b_R(p) <= chi^N_p m_R(p)` and `B^N_p <= chi^N_p chi_p`. That artifact records
  them as unproved for nonamenable `N`.
- **A per-cluster criterion for critical fibre l2.** Item 4 bounds the annealed
  operator `lambda_Q(sigma_(p_c))` by one number: the size-biased mean of the
  squared Kesten ratio of the cluster's shadow on `Q`. Bounding that number is
  the open claim `fpbs-critical-profile-kesten-ratio-integrable`. With the
  sandwich it gives the Kesten gap (route `fpbs-kesten-gap-via-profile-kesten-ratio`).
- **Trivial `N`.** Here `a = 1_K`, and item 4 reads
  `||T_p|| <= E_p[ ||lambda_Gamma(1_K)||^2 / |K| ]`.

**Calibration.** These are Sections 3 and 4 of the artifact.

- Items 1 and 3 fail for general nonnegative positive definite connection
  functions. On `F_2 x Z/2` with `N = F_2 x 0`, a normalised nonnegative positive
  definite `tau` has `sigma(1) = 1.08 > sigma(0) = 1`. So the proof must use
  partition structure, which mass transport supplies.
- Item 4 is not an equivalence. Finite-cluster invariant percolations confined
  to cosets of an amenable subgroup have `chi^N` finite and `||sigma||_Q`
  infinite. On them the Gram bound is infinite as well, so it detects that
  obstruction exactly.
