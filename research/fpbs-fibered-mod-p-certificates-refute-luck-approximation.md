---
rg: 2
id: fpbs-fibered-mod-p-certificates-refute-luck-approximation
kind: claim
title: A mod-p certificate of positive rank gradient for a free-by-cyclic or surface-by-cyclic group would refute positive-characteristic Lück approximation for the single matrix tI - J(phi)
distinct_from:
  fpbs-fg-by-cyclic-farber-chains-bounded-type-reduction: that reduces a counterexample to inner-type Farber chains with positive rank gradient; this shows the natural way to certify positive gradient on such chains, a lower bound on mod-p homology, is equivalent to breaking a conjecture about one explicit d x d matrix over F_p[Gamma].
  fpbs-quotient-split-actions-have-cost-one: that is the cost-one side of the counterexample; this is an obstruction on the cost-greater-than-one side.
artifacts:
  - research/fpbs-fibered-mod-p-certificates-refute-luck-approximation-proof.md
  - experiments/mapping-torus-inner-quotients-2026-09-17/foxnull.g
  - experiments/mapping-torus-inner-quotients-2026-09-17/foxnull.out
---

**ESTABLISHED (obstruction: unconditional bound and full-rank statement, plus a vanishing theorem conditional on a named conjecture).**
Proofs are in `research/fpbs-fibered-mod-p-certificates-refute-luck-approximation-proof.md`.

Let `Gamma = N x|_phi Z` with `N = F_d` or `N = pi_1(S_g)` (`d = 2g`), `k = F_p`,
and `B = tI - J(phi)` in `M_d(k[Gamma])`, where `J = (d phi(x_i)/d x_j)` is the
Fox Jacobian of the monodromy. For a finite quotient `G_n = Gamma/Gamma_n` write
`null(B_n)` for the left nullity of the image of `B` over `k[G_n]`.

1. **Fox block bound (unconditional).** For every finite quotient and every prime,
   `d_p(Gamma_n) - 1 <= null(B_n)`. For `N = F_d` the left side equals the nullity of
   the full Fox matrix. On inner-type chains, exactly
   `d_p(Gamma_n) = 1 + dim ker(psi_* - I)`, where `psi` is the lifted monodromy on
   `H_1(N cap Gamma_n; F_p)`. That space has dimension about `(d-1)|G_n|` (free case).
2. **Full rank (unconditional).** `B` is invertible over the twisted Laurent series
   division ring `D_N((t^-1; phi))`, so `rk_D(B) = d` for every Hughes-free division
   `k[Gamma]`-ring `D`.
3. **Conditional vanishing.** If positive-characteristic Lück approximation holds for
   `B` along a Farber chain, then `d_p(Gamma_n)/[Gamma:Gamma_n] -> 0` along that chain.
4. **What dies.** A counterexample to the fixed price problem among these groups,
   obtained through `fpbs-fg-by-cyclic-farber-chains-bounded-type-reduction`, cannot be
   certified by a linear lower bound on `d_p(Gamma_n)` for a fixed prime without
   refuting Lück approximation over `F_p[Gamma]` for the one matrix `tI - J(phi)`.
   A torsion certificate with the prime varying in `n` refutes the uniform form. So a
   proof of positive rank gradient here must bound `d(Gamma_n)` by genuinely
   non-abelian means (generation of perfect quotients), as the PSL_2(q) levels require.
5. **Unconditional constraints on the tower.**
   - Along a refinement by `p`-group layers the normalized nullity of any matrix, and in
     the free case `(d_p - 1)/index`, is non-increasing (Nakayama).
   - For inner-type chains `G_n^ab` is a quotient of `coker(phi_ab - I)`. So for the
     figure-eight monodromy `a -> ab, b -> bab` every level is perfect, and no chain can
     begin with a `p`-layer.
6. **Calibrations.** `phi = id` gives `null(B_n)/|G_n| = d/ord(t_n) -> 0` unconditionally.
   In characteristic 0 Lück's theorem gives `b_1/index -> 0`, consistent with 3.
   `foxnull.out` checks the identity in 1 and the bound at the first inner-type `PSL_2(7)`
   and `PSL_2(8)` levels of the figure-eight mapping torus.

**Scope.**
- The status of positive-characteristic Lück approximation for free-by-cyclic or
  surface-by-cyclic groups along arbitrary Farber chains is not established in this repo.
  Item 3 is conditional on it.
- Known positive-characteristic approximation results cover residual RFRS towers.
  Fisher–Hughes–Leary (arXiv 2212.03187) prove equality for RAAGs and Bestvina–Brady groups
  and an inequality for RFRS groups. Those towers have abelian layers, and item 5 shows
  inner-type figure-eight chains have none at the bottom. So the chains that matter here,
  with perfect `PSL_2(q)`-type levels, are outside what those results cover.
- Items 1, 2, 5 and 6 are unconditional.
- The obstruction concerns homological certificates only. It does not bound `d(Gamma_n)`
  itself, so it does not kill the reduction's criterion `RG(X) > 0`.

## Attempts

* **Mod-p homology as a rank-gradient certificate on inner-type levels.** This is the route
  the obstruction addresses. **Where it dies:** item 4. A linear lower bound on `d_p` is a
  counterexample to Lück approximation for `tI - J(phi)`, and item 5 rules out starting a
  figure-eight chain with `p`-layers.
