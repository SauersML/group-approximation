---
rg: 2
id: toms-simple-algebra-has-no-block-diagonal-rank-realizer
kind: claim
title: In Toms's simple no-Gamma algebra B no Cuntz-increasing realizer of tau(h), h non-constant, is block-diagonal from some stage on
distinct_from:
  toms-line-subalgebra-has-no-nonconstant-continuous-rank: that is the same theorem for the non-simple limit A with exact point traces; this runs it in B, through branch traces with constant contamination and point-evaluation blocks, with constants delta^2.
  toms-schubert-algebra-has-a-non-constant-continuous-rank: that is the open constructive claim for B; this rules out every construction whose containments never move support between copies.
  doubling-ah-finite-stage-continuous-ranks-are-constant: that excludes finite-stage elements and orthogonal sums in B; this excludes all block-diagonal Cuntz suprema.
---

Let `B = lim (B_i, psi_i)`, `B_i = s_i (C(X_i) tensor K) s_i`, be Toms's
Proposition 4 algebra (arXiv:2606.12188v2). Here `psi_i = psi_i^top + psi_i^pt`,
`alpha_i` is the top fraction and `delta = prod alpha_i > 0`. Put
`r_i = rank s_i` and `beta_n = prod_(i >= n) alpha_i >= delta`. For `x in X_n` let
`sigma_x` be the branch trace with stage-`n` measure `beta_n delta_x + kappa_n`,
where `kappa_n` does not depend on `x`
(`doubling-ah-finite-stage-continuous-ranks-constant-proof`, Step 1).

For `M > n`, `psi_(n,M)` is an orthogonal sum of
- `K` **top blocks** `Q_b`, pullbacks along the `K` coordinate projections
  `X_M = (X_n)^K x P -> X_n`, twisted by line bundles, with `K r_n = r_M prod_(n<=i<M) alpha_i`;
- **point blocks**, constant evaluations at fixed points, possibly twisted.

**Theorem.** Let `h in C(X_1)`, `0 <= h <= 1`, be non-constant with range `rho`,
and `f(tau) = tau(h)`. Let `a_m in M_infinity(B_(N_m))_+` be Cuntz-increasing with
`d(a_m) -> f` uniformly, and put `eps_m = sup_tau (f - d(a_m))`. Suppose that for
some `n` every later `a_M` is block-diagonal over these blocks, and every block
dominates its inherited block. For top blocks this reads
`rank (Q_b a_M Q_b)(w) >= R_n(w^(b))`. Then

```text
eps_M >= beta_n / (2 r_n) >= delta / (2 r_n)   for every M > n,     provided   delta rho >= 3 eps_n.
```

Since `eps_n -> 0`, some `n` qualifies, and `eps_M -> 0` fails. So **no such
realizer exists**. In particular the line subalgebra of `B` (pushforwards of
the coordinate lines of `theta^d` and of point-block lines) contains no element
of rank `tau(h)`.

**What changes from `A`.**
- *Contamination cancels.* `d_(sigma_w)(a) = beta_M rank a(w)/r_M + integral rank a/r_M d kappa_M`.
  Containment makes the contamination term of `a_M` at least that of the
  pushforward of `a_n`, so the budget still reads
  `sum_blocks (excess) <= r_M eps_n / beta_M`.
- *Profile range.* `f(sigma_x) = beta_n prod_(i<n) alpha_i F_n(x) + const = delta F_n(x) + const`,
  so the range over `X_n` is `delta rho`. The factors `beta_n / beta_M` and
  `r_M / r_n` cancel against the top fraction, which leaves `K` exactly in the
  violator count.
- *Point blocks are harmless.* They are constant in `w`, their excess is
  non-negative, and their ranks are lower semicontinuous, so they only add to
  the jump.

**Consequence for the Rank Problem candidate.** If `tau(h)` is a rank in `B`
(for instance if all ranks occur), then every realizer carries support between
top copies at arbitrarily late stages. These carries are sections of twisted
Hom bundles over the projective factors of internal nodes. Carries made
uniformly across copies lose everything at one point
(`toms-twisted-swap-pairs-are-totally-degeneracy-forcing`). So the Rank Problem
in `B` now rests on copy-dependent carries.

**Model test.**
- *Constant contamination is load-bearing.* If `kappa_n` depended on `x`, the
  contamination terms of `a_M` and of the pushforward of `a_n` would no longer
  compare pointwise, and the budget would fail.
- *Real object.* Toms's `B` satisfies `delta > 1 - eta > 0`.

Proof: `toms-simple-algebra-no-block-diagonal-realizer-proof`. Internal
derivation, unreviewed.
