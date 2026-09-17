---
rg: 2
id: rational-witnesses-miss-torsion-mean-dimension
kind: claim
title: Rational cohomological witnesses cannot certify rc >= mdim/2 (minimal subshifts over torsion alphabets)
distinct_from:
  stw99-problem-xxxvi-phillips-toms: that is the equality rc = mdim/2 itself; this is an obstruction theorem against the known general lower-bound mechanisms for its `>=` half, and says nothing about rc directly.
artifacts:
  - research/rational-witnesses-miss-torsion-mdim-proof.md
---

Let `K` be a finite-dimensional compact metric space of **basic type**
(`dim K^2 = 2 dim K`, Tsukamoto) and let `0 < rho`, `eta > 0` with
`rho + eta < 1`. There is a **minimal** subshift `X ⊂ K^Z` (with the shift
`sigma`) and a number `rho_inf in [rho, rho+eta]` such that

1. `mdim(X, sigma) = rho_inf · dim K`, and in fact
   `mdim(X, sigma) >= rho_inf · dim_F K` for every field `F`;
2. for every commutative field `F`, the Hirshberg--Phillips mean
   cohomological independence dimension (arXiv:2009.13045, Def. 2.9)
   satisfies `mcid(sigma|X ; F) <= rho_inf · dim_F K`.

More generally (Theorem B of the proof file), for every subshift
`X ⊂ K^Z` with `dim_F K < ∞`,
`mcid(sigma|X ; F) <= wd_F(X) := lim_n max_{|I|=n} dim_F pi_I(X) / n`,
the mean `F`-cohomological window dimension.

**Corollaries.**

* `K = (Pi_p)^s`, a product of `s` Pontryagin surfaces
  (`dim = dim_{Z/p} = 2s`, `dim_Q <= s`):
  `mdim(X) = 2s rho_inf` is arbitrarily large, while
  `mcid(sigma|X ; Q) <= mdim(X)/2`.
* `K` a Dranishnikov compactum realizing the Bockstein function
  `dim_Q = 1`, `dim_{Z/p} = dim_{Z_(p)} = n`, `dim_{Z/p^inf} = n-1`
  (all other primes `1`), if one takes the finite-dimensional realization
  theorem as given: `mcid(sigma|X ; Q) <= mdim(X)/n`.

Hence on these minimal systems both Hirshberg--Phillips lower bounds certify
at most `mcid(Q)/2`. The bounds are `rc >= m - k/2` with `m < mcid_k(Q)`,
and `rc >= m` with `m < mcid^gs_k(Q)/2`, where `mcid^gs_k <= mcid_k`. So they
give at most `mdim/4`, resp. `mdim/(2n)`, against the conjectured `mdim/2`.
Any proof of the Phillips--Toms `>=` inequality on these systems must use
witnesses that rational cohomology cannot see: **torsion** (mod-`p`) and
**relative** characteristic classes. The exact failing step is clause (1) of
the mcid definition. A nonzero rational cup product of `F_0`-translates of a
degree-`k` class forces
`k|F_0| <= dim_Q pi_{F+[-r,r]}(X) <= (rho_inf dim_Q K + o(1)) |F|`.

## Attempts

* Dichotomy: [Niu] gives `rc <= mdim/2 = rho_inf` for `K = Pi_p`. So either
  torsion witnesses give `rc = rho_inf`, or these explicit minimal systems
  are counterexamples to Phillips--Toms.

* Proposed ESTABLISHED via `rational-witnesses-miss-torsion-mdim-proof`
  (self-contained construction; cites Tsukamoto's uniform widim lemma,
  whose proof works for any field `F` with `q = dim_F K`, and Dranishnikov's
  cohomological-dimension theory and Pontryagin surfaces).
* Loophole (open): Tsukamoto's witnesses `(K,A)^n` with `Z/p` coefficients
  certify the full `mdim`. In top degree `q = dim K` the mod-`p` reduction
  `H^q(K,A;Z) -> H^q(K,A;Z/p)` is onto, so for `K = Pi_p` these lift to
  relative first Chern classes of line bundles trivialized on `A`. The gate
  for `>=` on these systems is to turn the relative torsion Euler classes of
  the Villadsen sums `⊕ pr_i^* L` into Cuntz non-comparison in the
  orbit-breaking subalgebra, with `O(1)` loss independent of `dim K`.
