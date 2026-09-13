---
rg: 2
id: toms-schubert-algebra-has-no-small-joins
kind: claim
title: In Toms's no-Gamma AH algebra two compact Cuntz classes of equal constant rank have no common upper bound of small rank
distinct_from:
  toms-ah-counterexample-to-uniform-gamma: that imports Toms's failure of uniform property Gamma, proved by non-equivalence of equal-trace projections in the uniform tracial completion; this is a Cuntz-semigroup statement that every common Cuntz upper bound of the two classes is large at some extreme trace.
  doubling-ah-finite-stage-continuous-ranks-are-constant: that is the branch-trace firewall on continuous ranks of orthogonal finite-stage sums; this uses the same branch traces together with Toms's Thom--Porteous degeneracy to bound common upper bounds from below.
  toms-schubert-algebra-misses-a-rank: that is the open question whether all ranks occur in the same algebra; this proves that Thiel's route to realizing ranks breaks down there.
---

Let `B = lim (B_i, psi_i)` be Toms's simple AH algebra
(arXiv:2606.12188, `prop:sparse-simplefication-survival`), with
`delta = prod_r alpha_r > 1 - eta`. Let `p_m in M_k(B_m)` and
`q^_m = q_m direct_sum 0` be Toms's projections, both of constant fibre rank
`d_m`, and put `t_m = d_m / rank(s_m)`. Every trace gives
`d_tau([p_m]) = d_tau([q^_m]) = t_m`.

**Theorem.** If `c in Cu(B)` satisfies `[p_m] <= c` and `[q^_m] <= c`, then
some extreme trace `sigma` has

```text
d_sigma(c) >= 2 t_m prod_(r >= m) alpha_r >= 2 delta t_m > 2 (1 - eta) t_m.
```

Thiel's dual Edwards condition (arXiv:1711.04721, `prp:EdwardsDual`, valid in
every unital C*-algebra) makes the infimum of `d_lambda(c)` over common upper
bounds `c` equal to `t_m` at each single extreme `lambda`. So the defect is
purely a failure of uniformity across the simplex. Small upper bounds exist
trace by trace, but no one element is small at every trace.

**Corollary (Thiel's Step 4 fails in `B`).** Suppose `eta < 1/4` and put
`f = (5/4) t_m`, a constant function. Both compact classes lie in Thiel's set

```text
L'_f = { a' : a' << a for some a with d(a) << f }.
```

A common upper bound `c'` in `L'_f` would give `c >= c'` with
`sup d(c) < (5/4) t_m < 2 delta t_m`. That contradicts the theorem, so `L'_f` is
not upward directed. In Thiel's section `sec:rankCu` this set is proved upward
directed for weakly cancellative, countably based, simple, stably finite,
non-elementary Cu-semigroups satisfying (O5), (O6+) and Edwards' condition.
Every property in that list except weak cancellation and (O6+) holds for
`Cu(A)` of every separable unital simple non-elementary stably finite `A`
(Thiel, proof of `prp:realizeChiselCa`, and `prp:EdwardsCa`). Hence **`Cu(B)`
fails (O6+) or fails weak cancellation**, and the maximal soft element
`alpha(f) = sup L'_f` of Thiel's proof does not exist as a supremum of `L'_f`.

This does not refute rank realization. The constant `f` is a rank in `B`, a
countable sum of projections. It shows that the stable-rank-one mechanism, namely
upper bounds with controlled rank below a target, is provably unavailable.

**Model test.** In a Z-stable algebra strict comparison gives an upper bound
of rank `(1 + eps) t_m` for any two classes of rank `t_m`, so the theorem needs
the degeneracy-forcing pair. `B` satisfies it.

Proof: `toms-schubert-algebra-no-small-joins-proof`.
