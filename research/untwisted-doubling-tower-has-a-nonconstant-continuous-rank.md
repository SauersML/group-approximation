---
rg: 2
id: untwisted-doubling-tower-has-a-nonconstant-continuous-rank
kind: claim
title: In the untwisted version of Toms's doubling tower every leaf average tau(h) is a rank, realized by averaged ramps and dimension-two comparison
distinct_from:
  toms-schubert-algebra-has-a-non-constant-continuous-rank: that asks for a non-constant continuous rank in Toms's twisted simple algebra B; this realizes one in the tower with trivial twists, as a calibration any obstruction for B must fail.
  toms-line-subalgebra-has-no-nonconstant-continuous-rank: that kills block-diagonal realizers in both towers; this exhibits a realizer in the untwisted tower whose containments rotate support between the two top copies, so that firewall is sharp.
  toms-rank-bookkeeping-admits-monotone-realizer-profiles: that writes down fibre-rank profiles meeting every rank constraint; this implements the same profiles by operators in the untwisted tower, where the containments exist by comparison over a square.
  toms-diagonal-quotient-has-nonconstant-continuous-ranks: that realizes ranks on a quotient where all leaf coordinates coincide; this realizes them against every trace, with independent leaves, but without twists.
---

**Setting.** Let `X_1` be compact metrizable, `X_(N+1) = X_N x X_N x Y_N` with
`Y_N` compact (for instance `CP^(j_N)`, ignored by the maps), `r_N = 2^(N-1) d`,
`A^u_N = M_(r_N)(C(X_N))` and `phi_N(a) = diag(pi_1^* a, pi_2^* a)`. Put
`A^u = lim (A^u_N, phi_N)`. This is Toms's Section 4 tower
(arXiv:2606.12188v2) with every line-bundle twist replaced by the trivial bundle.
For `h in C(X_1)` with `0 <= h <= 1`, let `F_N(x) = 2^(1-N) sum_l h(x_l)` be the
leaf average on `X_N`.

**Theorem.** There is `a in (A^u tensor K)_+` with `d_tau(a) = tau(h)` for every
`tau in T(A^u)`. It is the supremum of the Cuntz-increasing sequence
`a_N = g_N(F_N) in A^u_N`, where

```text
g_N(u) = diag_(k = 1..r_N) min(1, (r_N u - 1 - k)_+),     rank g_N(u) = R_N(u) = max(0, ceil(r_N u - 2)).
```

If `X_1` is path-connected and `h` is non-constant, this rank is continuous
and non-constant on `T(A^u)`.

**How it escapes the firewalls.** Every approximant is a finite-stage element,
so its own rank is not continuous. The containment `phi_N(a_N) <~ a_(N+1)` is
not block-diagonal. The rank of `a_(N+1)` depends only on `F_(N+1)`, the mean
of the two copies' averages. Along a level set of that mean, the saturated
support of `phi_N(a_N)` passes from copy 1 to copy 2 while `a_(N+1)` keeps a
constant rank. The operators implementing the containment rotate support between
the copies. Robert's comparison theorem over the square supplies them.

**Model test.**
- *The firewalls are sharp.* `toms-line-subalgebra-has-no-nonconstant-continuous-rank`
  applies to `A^u` too, so every realizer here must move support between copies,
  and this one does.
- *The twists are what is left.* In Toms's tower the same rotation between the two
  top copies is a map between bundles twisted by `O(1)` and `O(2)`. By
  `toms-constant-rank-twisted-transport-costs-double-rank` no realizer of `tau(h)`
  in Toms's non-simple limit can do this at constant rank. So the calibration
  succeeds exactly where the twists are absent. Any proof of
  `toms-simple-algebra-realizes-no-leaf-average-rank` has to use the twists.
- *Known case reproduced.* Simple diagonal towers of this kind with point
  evaluations have stable rank one (Elliott--Ho--Toms), so all ranks occur there
  by Thiel. This theorem gives an explicit realizer, with no stable-rank input.

Proof: `untwisted-doubling-tower-nonconstant-rank-proof`. Internal derivation,
unreviewed.
