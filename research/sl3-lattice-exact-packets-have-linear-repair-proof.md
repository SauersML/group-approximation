---
rg: 2
id: sl3-lattice-exact-packets-have-linear-repair-proof
kind: route
title: Replace the small primary summand and charge the remaining denominator coordinate with one Weyl relation
target: sl3-lattice-exact-packets-have-linear-repair
requires:
  - sl3-primary-mass-has-a-uniform-quadratic-gap
  - odd-congruence-lambda-exact-sector-collapses
  - sl3-re-lambda-exact-coprime-face-is-unfaithful
artifacts:
  - research/artifacts/sl3-linear-lattice-to-actor-repair-2026-09-08.md
---

The primary theorem gives a primary-trivial projection `P`, commuting with
`sigma(C)`, with `q=tr(1-P)<=C_p epsilon_D^2`. Define

    sigma_0(c)=P sigma(c)P+(1-P).

It is an exact coprime congruence representation in dimension `d`, with
`sup_c||sigma_0(c)-sigma(c)||_2<=2 sqrt(q)`. Its overlap and Weyl defects,
with the same `H`, are at most `epsilon_D+4 sqrt(q)` and
`epsilon_W+8 sqrt(q)`, respectively.

Extend `sigma_0` by the coprime reduction map to `rho:A->U(d)` and put
`H_0=rho(h)`, `W=H_0*H`, `R=sigma_0(C)'`. The overlap surjects onto
the coprime quotient. Kazhdan projection for `D` gives

    beta=||W-E_R(W)||_2
      <=(epsilon_D+4 sqrt(q))/kappa_D.

For `W_ij=sigma_0(w_ij)W sigma_0(w_ij)*`, the expectation commutes with
`sigma_0(w_ij)`, hence `||W_ij-W||_2<=2 beta`. The exact congruence
slots obey `H_0 (H_0'')*=H_0'`. Substituting `H=H_0 W` in the
approximate Weyl relation and replacing `W_23,W_12` by `W` costs at
most `4 beta`. The left copies of `W` cancel, leaving

    ||H-H_0||_2=||W-I||_2
      <=epsilon_W+8 sqrt(q)+4 beta.

This proves `(LAR1)` and `(LAR2)`. For an asymptotic actor with a nearby
exact lattice restriction, fixed-word telescoping makes both packet
defects tend to zero. The repaired generator tuple is therefore close,
and word telescoping extends the convergence to every fixed actor
element. The actor has the same ultraproduct representation with exact
coprime lattice coordinates. The two established coprime claims give the
commutant and scalar-relative-matrix exclusions in the target.
