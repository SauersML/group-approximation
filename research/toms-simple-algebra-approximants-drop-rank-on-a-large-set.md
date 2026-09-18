---
rg: 2
id: toms-simple-algebra-approximants-drop-rank-on-a-large-set
kind: claim
title: In Toms's simple algebra B every finite-stage element sitting between a deep approximant of a leaf-average realizer and the target band drops rank on a swap family on a set of real codimension at most 2m + 1, with the point-evaluation blocks cancelling
distinct_from:
  toms-swap-drop-locus-has-codimension-at-most-2m-plus-1: that proves the drop-locus transport bound and applies it in the non-simple limit A with exact point traces; this runs it in B through branch traces with constant contamination, where the point-evaluation blocks add an untwisted constant summand to both sides of the count.
  toms-simple-algebra-has-no-block-diagonal-rank-realizer: that excludes block-diagonal realizers through a trace-visible jump of K/2 ranks; this constrains every realizer, block-diagonal or not, but only through the geometry of the drop locus.
  toms-constant-rank-twisted-transport-costs-double-rank: that is constant rank in A; this is the drop-locus version in B.
  toms-simple-algebra-realizes-no-leaf-average-rank: that is the open target; this is a proved necessary condition on its realizers.
---

**Setting.** Let `B = lim (B_i, psi_i)`, `B_i = s_i (C(X_i) tensor K) s_i`, be Toms's
Proposition 4 algebra (arXiv:2606.12188v2), with
- `psi_i = psi_i^top + psi_i^pt`, top fractions `alpha_i`, `delta = prod alpha_i > 0`,
  `r_i = rank s_i`, and `beta_M = prod_(i >= M) alpha_i`;
- branch traces `sigma_w`, `w in X_M`, with `d_(sigma_w)(e) = beta_M rank e(w)/r_M + C(e)` for
  `e in M_infinity(B_M)_+`, where `C(e) = integral rank e / r_M d kappa_M` and `kappa_M`
  does not depend on `w` (`doubling-ah-finite-stage-continuous-ranks-constant-proof`).

The telescoped top map `psi_(M-1)^top` ends with a Section 4 doubling, so
`X_M = Y x Y x CP^j`, with twists `gamma_1, gamma_2` from `O(1), O(2)`. Here
`j = 2 (rank q_M / 2)^2 >= delta^2 r_M^2 / 2`.

Let `h in C(X_1)`, `0 <= h <= 1`, and let `c : [0,1] -> X_1` be an embedded arc with
`g(s) := h(c(s)) < g(1) = max h` for `s < 1`. Such an arc exists whenever `h` is non-constant.
Put

```text
Delta = g(1) - max_s (g(s) + g(1 - s))/2  >  0.
```

Let `xi(s) in Y` be the diagonal branch point over `c(s)`: every leaf is `c(s)`, and the
projective coordinates are fixed. The **swap family** is `K_M = Z_M x CP^j`, with
`Z_M = {(xi(s), xi(1 - s))}`.

**Theorem.** Suppose `a in (B tensor K)_+` has `d_tau(a) = tau(h)` for all `tau in T(B)`.
Then there are a stage `N` and `b in M_infinity(B_N)_+` with `b <~ a` such that for
every `M > N` the following holds. Let `a'' in M_infinity(B_M)_+` satisfy
`psi_(N,M)(b) <~ a''` and `d_tau(a'') <= tau(h)` for all `tau`, and let `m` be the
maximal rank of `a''` on `K_M`. Then `m <= r_M / delta`, and the drop set
`D = {rank a'' < m} ∩ K_M` satisfies

```text
dim D  >=  2j - 2m  >=  delta^2 r_M^2 - 2 r_M / delta.
```

In particular no such `a''` has constant rank on `K_M` once `r_M > 2/delta^3`.
Every finite-stage element `a''` with `psi_(N,M)(b) <~ a'' <~ a` qualifies. So every
deep approximant of a realizer loses rank on a subset of codimension at most
`2 r_M/delta + 1` in the `(2j+1)`-dimensional swap family.

**What changes from `A`.**
- *Point blocks cancel.* `psi_(M-1)^pt` gives the same constant untwisted summand
  `Π` on both endpoint slices. It enters the transport count as `θ^π` and the rank
  bands as `+π`, and it drops out of the comparison.
- *Contamination cancels.* `psi(b) <~ a''` gives `C(a'') >= C(psi(b))`, so the
  constant terms of the two bands compare in the right direction.
- *Profile.* `f(sigma_w) = delta F_M(w) + c_*`, where `F_M` is the top leaf average.
  The margin is `delta Delta` instead of `Delta`.

**What it does not do.** Depth-one drops are invisible to traces, which see them as
`beta_M / r_M`. `toms-chern-swap-count-allows-depth-one-drops` shows that the count
cannot force deeper drops. So this is a necessary condition on realizers, not the
obstruction.

Proof: `toms-simple-algebra-large-drop-locus-proof`. Internal derivation, unreviewed.
