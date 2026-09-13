---
rg: 2
id: toms-monotone-block-rounding-obeys-a-miranda-granularity-bound
kind: claim
title: A block-diagonal Cuntz-increasing realizer in Toms's tower cannot sharpen past one stage-n line per copy until it has range(h)/eps_n copies, so its precision decays no faster than r^(-0.618)
distinct_from:
  toms-rank-bookkeeping-admits-monotone-realizer-profiles: that shows total rank counts never obstruct; this shows per-copy monotonicity of ranks does obstruct, through a Poincare-Miranda all-wall point.
  toms-block-diagonal-sharpening-has-fuzz-persistence: that is the fractional-trace, bounded-displacement version for near projections; this is the integer-rank version for monotone realizers, where the slack budget itself bounds the displacement.
  toms-diagonal-subalgebra-supports-a-nonconstant-continuous-rank: that is the open existence question for realizers in the line subalgebra; this is a proved quantitative constraint on all of them.
---

Let `A = lim (A_N, phi_N)` be Toms's non-simple limit (arXiv:2606.12188v2,
Section 4), `r_N = rank q_N`, `h in C(X_1)` with range `rho = max h - min h > 0`,
`f(tau) = tau(h)` and `F_N(x) = 2^(1-N) sum_l h(x_l)`. For `M > n` let `Q_b`,
`b = 1..K`, `K = 2^(M-n)`, be the copy projections of `phi_(n,M)`, amplified.

**Setting.** `a_n in M_infinity(A_n)_+` and `a_M in M_infinity(A_M)_+` have fibre
ranks `R_n, R_M` with pointwise sandwiches
`r_m (F_m - eps_m) <= R_m <= r_m F_m` (`m = n, M`). This is what uniform
convergence of ranks gives at point traces. Assume `a_M` is **block-diagonal
and dominates blockwise**:
`a_M = sum_b Q_b a_M Q_b` and `rank (Q_b a_M Q_b)(w) >= R_n(w^(b))` for all `w, b`.

**Theorem.** If `r_n (rho - K eps_n) >= 2`, then `eps_M >= 1/r_n`.

So a block-diagonal monotone step from stage `n` gains nothing beyond the
stage-`n` granularity until `K > rho/eps_n`.

**Corollary (golden rate).** Let `(a_m)` be a Cuntz-increasing realizer of `f`
whose containments are all block-diagonal in this sense, with precisions `eps_m`.
If `eps_m <= C r_m^(-gamma)` for all large `m`, then
`gamma <= (sqrt 5 - 1)/2`.

**Where it applies.** Every realizer inside the line subalgebra `D` of
`toms-diagonal-subalgebra-supports-a-nonconstant-continuous-rank`. There
Cuntz comparison is support inclusion line by line, and lines lie inside copies.

**Mechanism.** Per-copy monotonicity plus the slack budget bounds how far a
copy's rank can sit above its inherited rank, by at most `K r_n eps_n` lines. With
that bound, the Poincare–Miranda theorem gives an **all-wall point**: every
copy has rank `<= k`, and arbitrarily close by every copy has rank `>= k + 1`.
The count jumps by `K` there, which the band must absorb. This is the
"monotone rounding at a point where every copy sits at a wall" of the brief,
made exact. The slack does **not** run out: for `K > rho/eps_n` a few copies can
carry macroscopic delays, and the theorem says nothing.

**Model test.**
- *Independence of copies is load-bearing.* On the diagonal quotient all copies
  coincide, the path product used in the proof does not exist, and the
  uniformly distributed element realizes `tau(h)`.
- *Block-diagonality is load-bearing.* For a general containment,
  compressions `Q_b a_M Q_b` need not dominate `Q_b phi(a_n) Q_b` in the Cuntz
  order. That is exactly where transports between twisted copies live.
- *Real object.* Every element of `D` in Toms's tower satisfies the hypotheses,
  in both the twisted and the untwisted tower.

Proof: `toms-monotone-block-rounding-miranda-bound-proof`. Internal derivation,
unreviewed.
