---
rg: 2
id: lifted-thompson-t-mf-descent-via-central-eigencorners
kind: route
title: A commutant eigencorner in every representation gives MF descent from T-bar to T
target: lifted-thompson-t-mf-descends-to-t
requires:
  - lifted-thompson-t-centre-has-commutant-eigencorners
  - lifted-thompson-t-twist-set-is-trivial-or-the-circle
---

**Proof.**  Suppose `T̄` is MF.  Then some corona representation `rho` has
`rho(z) != 1`.
1. By `lifted-thompson-t-centre-has-commutant-eigencorners` there are a
   nonzero projection `P in rho(T̄)' ∩ Q` and `lambda != 1` with
   `rho(z) P = lambda P`.
2. The corner representation `rho_P` (Steps 1a–1b of
   `central-eigencorners-die-over-full-radical-quotients-proof`) has
   `rho_P(z) = lambda 1`.  So `lambda in Sigma \ {1}`.
3. By item 2 of `lifted-thompson-t-twist-set-is-trivial-or-the-circle`,
   `T` is MF.

∎

This route uses (EC) for a single representation only.  That is the
quantifier gap between (EC) and its target.
