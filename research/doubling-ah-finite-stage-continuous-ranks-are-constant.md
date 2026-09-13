---
rg: 2
id: doubling-ah-finite-stage-continuous-ranks-are-constant
kind: claim
title: In doubling AH systems with connected spectra, finite-stage elements and their orthogonal sums have continuous ranks only when the rank is constant
distinct_from:
  toms-doubling-ah-trace-simplex-is-poulsen: that computes the trace simplex of doubling systems and shows the extreme boundary is dense; this uses the branch traces with constant contamination to show that finite-stage rank functions are step functions along them, hence continuous only when constant.
  all-ranks-occur-iff-continuous-ranks-are-dense: that is the general criterion that all ranks occur iff continuous ranks are dense; this shows that in doubling systems no finite-stage element and no countable orthogonal sum of them supplies a non-constant continuous rank.
---

**Setting.** `A = lim (A_i, phi_i)` is unital with
`A_i = s_i (C(X_i) tensor K) s_i`, where each `X_i` is compact metrizable and
**connected** and `s_i` has constant rank `r_i`. For `y in X_(i+1)` the fibre
trace at `y`, composed with `phi_i`, is the measure

```text
P_i(y) = alpha_i |W_i|^(-1) sum_(w in W_i) delta_(lambda_(i,w)(y)) + (1 - alpha_i) nu_i,
```

with finite `W_i`, continuous `lambda_(i,w): X_(i+1) -> X_i`,
`sum_i (1 - alpha_i) < infinity`, and a probability measure `nu_i` **that does
not depend on `y`** (constant contamination). There are continuous maps
`d_i: X_i -> X_(i+1)` with `lambda_(i,w) o d_i = id` for every `w` (diagonal
points).

**Theorem.** Let `a in (A tensor K)_+` be either the image of a positive
element of `M_k(A_N)` for some `N` and `k`, or a countable orthogonal sum of
such images. If `tau -> d_tau(a)` is finite and continuous on `T(A)`, it is
constant. In the finite-stage case, for every `M >= N` with
`prod_(s >= M) alpha_s > 0`, the pushed-forward element has constant fibre rank
on `X_M`.

**Instances.** Toms's simple AH algebra `B` without uniform property Gamma
(arXiv:2606.12188v2, Proposition `prop:sparse-simplefication-survival`) and the
non-simple limit of its Section 4 satisfy the setting:
- the spectra `X_1 = Gr(d,2d)` and `X_(i+1) = X_i x X_i x CP^(j_i)` are
  connected;
- the top maps are pullbacks along composites of coordinate projections,
  twisted by line bundles, and the diagonal `(x, x, point)` is a common section;
- `psi_i^pt` is a finite direct sum of point evaluations, so its contamination
  measure does not depend on `y`;
- Toms arranges `sum (1 - alpha_i) < infinity`.

**Model test of the hypotheses.** Connectedness is load-bearing. If some `X_M`
had two components, a projection supported on one of them would have a
continuous, non-constant rank function. Constant contamination is used to make
the non-branch part of every branch trace independent of the base point.

**Consequence.** Every continuous rank function that can be built as a
countable orthogonal sum of finite-stage pieces is constant. This covers
projection sums, the Brown--Perera--Toms layer-cake sums, and the Edwards
increment method of `all-ranks-occur-iff-continuous-ranks-are-dense`. So in `B`
a non-constant continuous affine function can be a rank only through a
Cuntz-increasing sequence of finite-stage elements whose increments are not
orthogonal summands. See `toms-schubert-algebra-misses-a-rank`.
