---
rg: 2
id: lifted-thompson-t-corona-centre-spectrum-is-full-circle
kind: claim
title: If Thompson's T has a uniform op-norm defect gap, then every nontrivial corona representation of T-bar has full-circle central spectrum, at every dilation level and in every commutant corner it moves
distinct_from:
  lifted-thompson-t-centre-has-commutant-eigencorners: that asks for an exact commutant eigencorner of rho(z) whenever rho(z) != 1; this shows that, under the T gap, no nontrivial corner can even have a spectral gap in its central unitary, so every eigencorner, and every corner cut from C*(rho(z)), is a corner that rho fixes.
  central-eigencorners-die-over-full-radical-quotients: that kills exact eigencorners, that is isolated points of sp(rho(z)), over a full-radical quotient; this kills every clopen piece of sp(rho(z)) shorter than an explicit arc alpha_0, and then, using the dilation of T-bar, every spectral gap at all.
  lifted-thompson-t-mf-radical-dichotomy: that shows Rad(T-bar) is 1 or T-bar and relates it to T; this is a quantitative statement about the central unitary of each nontrivial representation, conditional on the T gap.
---

**ESTABLISHED** by `lifted-thompson-t-corona-centre-spectrum-is-full-circle-proof`
(written proof; not Lean-verified).  It is an implication.  Its hypothesis is the
uniform gap of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`, which is
equivalent to the OPEN claim `thompson-t-has-full-mf-radical`.

## Setting

- `T̄`, `z`, `a`, `b` are as in `funar-sergiescu-lifted-thompson-t-is-t311`:
  `a^4 = b^3 = z`, `(ba)^5 = z^3`, `r_1(a,b) = r_2(a,b) = 1`, and `a, b` generate `T̄`.
- `lambda(g)(x) = g(2x)/2` is the dilation, an injective endomorphism of `T̄`.
  `t_k = lambda^k(z)` is translation by `2^(-k)`, so `t_0 = z` and `t_(k+1)^2 = t_k`.
- A *corona* is `Q = prod_n M_(k_n) / (+)_n M_(k_n)`.  Some `k_n` may be `0`, so every
  corner `PQP` of a corona is again a corona.
- `D(A,B)` and the relators `r_1, r_2, r_P = (ba)^5` are as in
  `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`.
- **`G(eps_0)`** says that every exact pair `(A,B) in U(n)^2`, for any `n`, with
  `A^4 = B^3 = 1` and `D(A,B) < eps_0` is `(1,1)`.
  - Some `G(eps_0)` holds iff `T` is not MF (item 3 of the criterion).
  - Necessarily `eps_0 <= delta_1 = 2 sin(pi/12)`.
- `alpha_0 = min(pi, 24 arcsin(eps_0/2))`, which is positive.

## Statement

Assume `G(eps_0)`.  Let `rho : T̄ -> U(Q)` be a homomorphism into a corona, and put
`C = rho(z)`.

1. **Central twist lemma.**  If `sp(C)` lies in the arc `{e^(i theta) : |theta| <= alpha}`
   for some `alpha < alpha_0`, then `rho` is trivial.
2. **Short pieces die.**  Suppose `S_1` is a clopen subset of `sp(C)` contained in a
   closed arc of length `< alpha_0`, and `P = chi_(S_1)(C)`.  Then `P rho(g) = P` for
   every `g`, and `S_1` is contained in `{1}`.
   - Consequently every connected component of `sp(C)` is either `{1}` or an arc of
     length `>= alpha_0`.
3. **Full circle at every level.**  If `rho` is nontrivial, then `sp(rho(t_k)) = S^1`
   for every `k >= 0`.  In particular `sp(rho(z)) = S^1`.
4. **Corners.**  Let `P` be a nonzero projection in `rho(T̄)' ∩ Q` such that the corner
   representation `g -> P rho(g)` is not identically `P`.  Then `sp_(PQP)(rho(z) P) = S^1`,
   and likewise `sp_(PQP)(rho(t_k) P) = S^1` for every `P` in `rho(lambda^k T̄)' ∩ Q` on
   which `rho o lambda^k` acts nontrivially.
   - This includes the central projections `[chi_N']` of `Q`, which restrict to a
     subsequence `N'`.
   - **Levelwise form.**  Fix unitary lifts `u_n(g)` of `rho(g)` and `c_n` of `C`, an
     element `g` and `c > 0`, and suppose `N'' = {n : ||u_n(g) - 1|| >= c}` is infinite.
     Along `N''`, the finite spectra `sp(c_n)` converge to `S^1` in the Hausdorff metric.
     The same holds for lifts of `rho(t_k)`.
5. **Class kill: central functional-calculus twists.**  Let `rho` be nontrivial.  Then no
   unitary `u` in `C^*(C)` satisfies `u^12 = C`, and `C^*(C)` has no projections other
   than `0` and `1`.
   - The same holds after tensoring.  Take `p + q >= 1` and
     `sigma = rho^(⊗p) ⊗ conj(rho)^(⊗q)`, a corona representation of `T̄` in matrix size
     `k_n^(p+q)`.  Let `C_1, ..., C_(p+q)` be its commuting legs `1 ⊗ ... ⊗ C ⊗ ... ⊗ 1`,
     conjugated in the last `q` places.  No `u` in `C^*(C_1, ..., C_(p+q))` satisfies
     `u^12 = sigma(z) = C_1 ... C_(p+q)`.
   - The invariant is the degree vector `(1,...,1,-1,...,-1)` of `sigma(z)` on the joint
     spectrum, which is the whole torus `(S^1)^(p+q)` by the levelwise form of item 4.
     It is not divisible by `12`.  The exponent `12` comes from `a^4 = b^3 = z`, and the
     obstruction is that `(ba)^5 = z^3` leaves the residue `3 - 5/4 - 5/3 = 1/12`, which
     is the Euler number `1` divided by `12`.
   - So the twist of item 1 applies exactly to the representations that item 3 rules
     out, and nowhere else.

## Consequence for the flagship

`lifted-thompson-t-is-not-mf` is equivalent to `thompson-t-has-full-mf-radical` together
with (FC), where (FC) says that no nontrivial corona representation of `T̄` has
`sp(rho_P(t_k)) = S^1` at every level `k` and in every corner it moves.  Under the T gap,
(FC) is the entire residual.  An approach to
`lifted-thompson-t-centre-has-commutant-eigencorners` that cuts or twists `rho` using the
functional calculus of its central unitaries, whether `rho(z)`, `rho(t_k)` or their tensor
powers, cannot reach (FC).  A witness projection must come from outside
`C^*(rho(t_k) : k >= 0)` and its tensor powers.
