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

**Slice-wise form.** Telescoping makes each deep spectrum a product,
`X_n = (X_m)^L x (projective factors)`, whose leaf maps `lambda_l` are the
coordinate projections. For a leaf `l`, let `E_l` and `F_l` be the leaf-`l`
summands of `psi_(m,n)(p_m)` and `psi_(m,n)(q^_m)`. These are subprojections of
constant rank `t' = d_m / rank(s_n)`. A *slice* of leaf `l` is a set `S` on
which every coordinate except the `l`-th is fixed. If `c >= [E_l], [F_l]`, then
**on every slice `S` some `x in S` has `d_(sigma_x)(c) >= 2 beta_n t'`**. So
`L'_f` is not upward directed for any `f in LAff(K)_(++)` with `min f > t'`
and `f(sigma_x) < 2 beta_n t'` for all `x` in some slice. These targets need not
be constant. The obstruction is available at every scale `t_m / |L_(m,n)|`.

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
fails (O6+) or fails weak cancellation**. The disjunction is resolved on the
(O6+) side by the dual meet statement `toms-schubert-algebra-fails-o6-plus`:
common Cuntz lower bounds of the same pair keep a support gap, and functional
infima need only (O6+). Whether weak cancellation holds in `Cu(B)` is not
decided here. Either way the maximal soft element
`alpha(f) = sup L'_f` of Thiel's proof does not exist as a supremum of `L'_f`.

**Corollary (no maximal soft realizer below `f`).** The soft classes `x` with
`d(x) <= f = (5/4) t_m` have no largest element. Adding a soft class of rank at
most `t_m/4` to `[p_m]` or `[q^_m]` gives soft classes of rank at most `f`. A
largest such class would dominate both and have rank at most `f`
everywhere, contradicting the theorem. So Thiel's Galois connection
`alpha -| kappa` between `LAff(K)_(++)` and the soft part of the Cuntz semigroup
does not exist in `B`. In the language of
`rank-density-and-small-joins-give-all-ranks`, `B` has rank density but fails
small joins, and lies exactly outside that cell.

This does not refute rank realization. The constant `f` is a rank in `B`, a
countable sum of projections. It shows that the stable-rank-one mechanism, namely
upper bounds with controlled rank below a target, is provably unavailable.

**Model test.** In a Z-stable algebra strict comparison gives an upper bound
of rank `(1 + eps) t_m` for any two classes of rank `t_m`, so the theorem needs
the degeneracy-forcing pair. `B` satisfies it.

Proof: `toms-schubert-algebra-no-small-joins-proof`.
