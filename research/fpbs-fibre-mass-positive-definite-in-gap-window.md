---
rg: 2
id: fpbs-fibre-mass-positive-definite-in-gap-window
kind: claim
title: Whenever the relative susceptibility of a normal subgroup is finite, in particular throughout the gap window below the relative threshold, the fibre mass is a positive definite function on the quotient that is maximal at the identity, its finite-cluster part is a coefficient of the regular representation, and on tree products that part obeys the square-root law
distinct_from:
  fpbs-two-point-fourier-algebra-criterion: that proves the two-point function tau_p is positive definite on Gamma and puts its finite-cluster part in A(Gamma); this is the fibre-summed kernel on the quotient Q = Gamma/N, which is not a formal consequence (the fibre sum of a nonnegative positive definite function over a nonamenable N can fail to be positive definite, Remark R of the proof), and in the gap window it needs a new root because the counting root 1/|K| does not exist for infinite clusters.
  fpbs-amenable-normal-fibre-mass-maximal-at-subgroup: that bounds sigma_p(q) <= sigma_p(e) for amenable normal subgroups by a Folner argument; this proves the same first-moment bound for every normal subgroup, amenable or not, by a coset transport and Cauchy-Schwarz, and adds positive definiteness.
  fpbs-normal-fibre-second-moment-maximal: that bounds the second fibre moment, E Y_q^2 <= E X^2, giving sigma_p(q) <= (E X^2)^(1/2); this bounds the first moment by the first moment and needs only chi^N_p < infinity.
  fpbs-quotient-l2-threshold-sandwich: that orders the threshold where convolution by sigma_p is bounded; this is positivity of sigma_p, which holds on the whole range chi^N_p < infinity, including where the convolution is unbounded.
  fpbs-relative-threshold-is-quotient-l2-threshold: that is the open Claim E; this proves a necessary positivity property on the gap window and the implication from E to the regular-coefficient condition of fpbs-gap-window-fibre-mass-in-fourier-algebra.
  fpbs-tree-product-fibre-square-root-law-below-relative-threshold: that is the open summable square-root law for the full fibre mass; this proves the pointwise square-root law for the finite-cluster part, so any failure of that law comes from infinite clusters.
artifacts:
  - experiments/fpbs-window-positive-definite-2026-09-17/check_gram_identity.py
  - experiments/fpbs-window-positive-definite-2026-09-17/check_gram_identity.out
---

**ESTABLISHED.** Proof in `fpbs-fibre-mass-positive-definite-in-gap-window-proof`.
The script only checks the identities of parts 1 and 2 by exact enumeration
on dihedral Cayley graphs, and the proof does not use it.

**Setting.**

- `G = Cay(Gamma,S)`, `N` a normal subgroup, `Q = Gamma/N`, and the law of
  the percolation is Bernoulli(`p`) bond percolation. The proofs of parts 1
  to 3 use only `Gamma`-invariance of the law.
- For a vertex set `C` and a coset `v in Q`, `A_C(v) = |C ∩ vN|`.
- The fibre mass is `sigma_p(q) = E_p A_(K_o)(q) = sum_(x in q) tau_p(o,x)`.
  `chi^N_p = sigma_p(e)`.
- For a cluster functional `psi >= 0` that is invariant under left
  translation by `N`, put `sigma_(p,psi)(q) = E_p[A_(K_o)(q) psi(K_o)]`. The
  cases used are `psi = 1`, `psi = 1{|C| < infinity}` (giving `sigma^fin_p`)
  and `psi = 1{|C| = infinity}` (giving `sigma^inf_p`).
- `y_v` is any element of the coset `v`, and `pi` is any probability measure
  on `Q` with `pi_v > 0` for all `v`. Put `W_pi(C) = sum_r pi_r A_C(r)`.

**Theorem.** Suppose `chi^N_p < infinity`. By `fpbs-hp-relative-sharpness`
this holds for every `p < p_c(N;G)`, so in particular on the whole gap window
`p_c(G) < p < p_c(N;G)`.

1. **(Maximality, every normal N.)** `sigma_p(q) = sigma_p(q^(-1))` and
   `sigma_p(q) <= sigma_p(e)` for all `q in Q`.
2. **(Probability-weighted Gram identity.)** For all `u, w in Q`, every `pi`
   as above and every `psi` as above,

   ```text
   sigma_(p,psi)(u^(-1) w) = sum_(v in Q) pi_v E_p[ A_(K_(y_v))(u) A_(K_(y_v))(w) psi(K_(y_v)) / W_pi(K_(y_v)) ],
   ```

   and `W_pi(K_(y_v))` lies in `[pi_v, infinity)` almost surely.
3. **(Positive definiteness.)** `sigma_(p,psi)` is a positive definite
   function on `Q`. In particular `sigma_p`, `sigma^fin_p` and `sigma^inf_p`
   are positive definite, and `sigma_p = sigma^fin_p + sigma^inf_p`.
4. **(Finite part is a regular coefficient.)** There is a vector
   `xi_fin` in `l2(Q) ⊗ L2(Omega)` with `||xi_fin||^2 = sigma^fin_p(e)` and
   `sigma^fin_p(q) = <xi_fin, (rho ⊗ 1)(q) xi_fin>` for all `q`, where
   `rho` is the right regular representation of `Q`. So `sigma^fin_p` lies in
   the Fourier algebra `A(Q)`.
5. **(What Claim E forces.)** If `||sigma_p||_Q < infinity` (the conclusion
   of Claim E below `p_c(N;G)`), then also `||sigma^inf_p||_Q < infinity`, and
   there is `xi_inf in l2(Q)` with `||xi_inf||^2 = sigma^inf_p(e)` and
   `sigma^inf_p(q) = <xi_inf, rho(q) xi_inf>`. This is the regular-coefficient
   condition (E1) of `fpbs-gap-window-fibre-mass-in-fourier-algebra`.
6. **(Tree products.)** In the setting of
   `fpbs-tree-product-fibre-operator-is-half-tilted-susceptibility`
   (`G = T x H`, `T` the `k`-regular tree, `N = H_grp`), write
   `f^fin_p(n)` and `f^inf_p(n)` for the values of `sigma^fin_p` and
   `sigma^inf_p` at tree distance `n`. For every `p` with `chi^N_p < infinity`
   and every `n >= 0`,

   ```text
   f^fin_p(n) <= (1 + n(k-2)/k) (k-1)^(-n/2) f^fin_p(0).
   ```

   The same bound holds for `f^inf_p` whenever `sigma^inf_p` is a diagonal
   coefficient of a multiple of `rho` (condition E1), and hence for `f_p`
   under Claim E.

**Why it matters.**

- It answers the open point left by the w18 Gram representation (commit
  34ec082853, not landed in this worktree), which proved positive
  definiteness only where clusters are finite and recorded that in the gap
  window "the Gram root 1/|K| does not exist, and no invariant substitute has
  been found". The substitute is the probability-weighted root
  `pi_v / W_pi`. It is positive but not `Q`-equivariant, and the equivariant
  choice `pi = counting measure` makes `W_pi = |C|`, which is infinite on
  infinite clusters.
- It corrects the dictionary row "`p < p_c(N;G)` iff the fibre kernel is
  `L^1`": what holds on the whole range below `p_c(N;G)` is
  `sigma_p in B(Q)^+` (part 3), and the `L^1`-type statement is membership
  in `A(Q)`, which is open (E1).
- It gives the chain **E ⇒ E1 ⇒ (positive definiteness, proved)**. E1 can
  fail on its own, and a failure refutes Claim E. On tree products E1 fails
  if some `p < p_c(N;G)` has fibre exponent `beta_fib(p) < 1/2`, and by part
  6 only infinite clusters can produce such a failure.
