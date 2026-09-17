---
rg: 2
id: kt-pair-c-rank-sofic-action-moves-fixed-algebra
kind: claim
title: Some C-rank-realized action of the Kun--Thom group moves a Gamma-invariant set by an element of EL_r(R)
distinct_from:
  c-linear-sofic-group-carries-nontrivial-rigid-defect: that asks for a unit in the relative commutant of sigma(Gamma) that some sigma(g) moves out of it; this asks for an involution in that commutant whose sigma(G)-conjugates commute pairwise and which sigma(N) moves, which is the Boolean special case and suffices through lamp quotients.
  kun-thom-wreath-linear-sofic: that asks for a faithful rank model of W, the strongest form of this claim, equivalent to C-rank-soficity of the generalized Bernoulli action; this asks only that the rank radical of W be strictly smaller than K_even.
  kt-wreath-rank-radical-is-rank-fixed-algebra-rigidity: that proves the equivalences and the payoff; this is the open witness statement.
refuted_by:
  - c-linear-sofic-groups-kill-rigid-compression-defects
---

**OPEN.** Let `Gamma = EL_r(R_+) < G = EL_r(R) x| SL_d(Z)` be the Kun--Thom Theorem E pair, with
`N = EL_r(R)` (`kun-thom-nonsofic-wreath`). The claim: some `C`-rank-realized p.m.p. action
`G ↷ (Y, nu)` has a `Gamma`-invariant Borel set `B` and an `n in N` with `nu(nB triangle B) > 0`.

## Equivalent forms

By [[kt-wreath-rank-radical-is-rank-fixed-algebra-rigidity]] each of the following is equivalent to the claim.

1. **Radical form.** `Rad_(rk,C)(W) != K_even` for the coset wreath `W`.
2. **Lamp-quotient form.** Some `C`-linear sofic lamp quotient `W/U` has a nontrivial seed
   defect.
3. **Matrix form.** There are a homomorphism `sigma : G -> U(R_omega)` into a complex rank
   ultraproduct and an idempotent `p in R_omega` such that:
   - `p` commutes with `sigma(Gamma)`;
   - the conjugates `sigma(g) p sigma(g)^(-1)` commute pairwise;
   - `sigma(n) p sigma(n)^(-1) != p` for some `n in N`.

   *Proof of 3 => 2.* Put `u_(g Gamma) = 1 - 2 sigma(g) p sigma(g)^(-1)`. This is well defined because
   `p` commutes with `sigma(Gamma)`. The `u_x` are commuting involutions permuted by `sigma(G)`, so
   `theta(f, g) = prod_(x in supp f) u_x sigma(g)` is a homomorphism `W -> U(R_omega)`, and
   `rk(theta(m_n) - 1) = rk(p - sigma(n) p sigma(n)^(-1)) > 0`. So `m_n notin Rad_(rk,C)(W)`, and Theorem 3
   of the equivalence node gives the claim.
   *Proof of 1 => 3.* Take the model of a `theta` with `theta(m_n) != 1`, and put `p = (1 - theta(e_o))/2`.

The strongest form is that the generalized Bernoulli action `G ↷ ({0,1}, fair)^(G/Gamma)`
is `C`-rank-sofic. That is equivalent to [[kun-thom-wreath-linear-sofic]].

**Payoff.** A witness makes the lamp quotient `W/N_mu` `C`-linear sofic and not sofic. That
answers [[linear-sofic-nonsofic-group]] (Arzhantseva--Paunescu Q8.5), and it proves
[[c-linear-sofic-group-carries-nontrivial-rigid-defect]].

## Attempts

- **Permutation realizations never witness.**
  - Realizations by permutation matrices and diagonal idempotents are sofic actions.
  - Kun--Thom Theorem C gives them `G`-invariant `Gamma`-fixed algebras.
  - So a witness must use non-monomial `sigma(G)` or non-diagonalizable families `E`.
- **Profinite actions never witness** (`profinite-action-fixed-algebra-invariant`). That result
  is about the action, whatever the realization. So the action must be non-profinite, and by
  Theorem C it must be nonsofic.
- **Algebraic models do not exist.** A ring of characteristic `p` has no unital map into a
  nonzero `C`-algebra. So `sigma` cannot come from a ring homomorphism `R -> R_omega`, and the
  normalization argument of `c-linear-sofic-group-carries-nontrivial-rigid-defect` does not apply.
- **What the matrix form adds.** The general defect node allows any unit of the relative
  commutant. Here the unit must be an involution whose `G`-orbit is commutative. Then rank is
  an invariant measure on the Boolean algebra that the orbit generates. This is the extra rigidity
  that a proof of [[c-linear-sofic-groups-kill-rigid-compression-defects]] could exploit first:
  - property (T) of `Gamma` and of `G` acting on that measure algebra;
  - Kun--Thom's Theorem C argument, run with rank in place of counting measure.
