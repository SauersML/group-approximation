---
rg: 2
id: toms-constant-rank-twisted-transport-costs-double-rank
kind: claim
title: In Toms's tower a containment whose target has constant rank along a swap family needs twice the swapped rank, so no realizer of a leaf average in the non-simple limit carries support between top copies at constant rank
distinct_from:
  toms-twisted-swap-pairs-are-totally-degeneracy-forcing: that shows a carry made uniformly in all copies loses the whole pushforward at one point; this bounds any Cuntz containment, copy-dependent or not, whose target has constant rank on a connected family of top slices, by counting Chern roots.
  toms-line-subalgebra-has-no-nonconstant-continuous-rank: that kills block-diagonal realizers by a Poincare–Miranda jump; this kills the non-block-diagonal rotation that the untwisted calibration uses, at constant rank.
  untwisted-doubling-tower-has-a-nonconstant-continuous-rank: that realizes every leaf average in the untwisted tower by a containment of constant rank r/2 - 2 along swap families; this proves the same step is impossible once the twists are nontrivial.
  toms-simple-algebra-realizes-no-leaf-average-rank: that is the target conjecture for the simple algebra B; this is a proved obstruction in the non-simple limit A, restricting how deep approximants of a realizer can look.
---

**Setting.** Let `A = lim (A_i, phi_i)` be the non-simple limit of Toms's
Section 4 (arXiv:2606.12188v2), with `A_i = M_(r_i)(C(X_i))`, `r_i = d_i`,
`X_(i+1) = X_i x X_i x CP^(j_i)`, `j_i = 2 d_i^2`, and
`phi_i(a) = pi_1^* a tensor gamma_1 + pi_2^* a tensor gamma_2`. Here `gamma_1`
and `gamma_2` are pulled back from line bundles `L_1, L_2` on `CP^(j_i)` with
`c_1(L_1) = alpha u` and `c_1(L_2) = beta u`, where `beta != 0` and `alpha != beta`.
Toms's twists `O(1), O(2)` qualify. A *top slice* of `X_M` is `{z} x CP^j` with
`z in X_(M-1)^2` and `j = j_(M-1)`.

**Theorem (transport bound).** Let `P, Q in M_k(A_M)_+` with `P <~ Q`. Let
`Z ⊂ X_(M-1)^2` be compact and connected, and suppose `rank Q ≡ m` on `Z x CP^j`
with `m <= j`. Let `z_0, z_1 in Z` and suppose that for `i = 0, 1` there is a
projection `e_i <~ P|({z_i} x CP^j)` whose range is `L_1^(p_i) ⊕ L_2^(q_i)`.
Put `s_i = m - p_i - q_i`. Then `s_0, s_1 >= 0` and

```text
q_0 - q_1  in  [ -s_0, s_1 ].
```

When `alpha != 0` as well, `p_0 - p_1 in [-s_0, s_1]` too.

**Swap corollary.** Let `a' in M_k(A_(M-1))_+`, `x, y in X_(M-1)`, and let
`Z ⊂ X_(M-1)^2` be compact and connected, containing `(x, y)` and `(y, x)`. If
`phi_(M-1)(a') <~ Q` and `rank Q ≡ m <= j` on `Z x CP^j`, then

```text
m  >=  2 max( rank a'(x), rank a'(y) ).
```

This is sharp: `Q = phi_(M-1)(a')` with `a'` a constant projection gives `m = 2 rank a'`.

**Consequence for leaf averages.** Let `X_1 = Gr(d, 2d)` and let `h in C(X_1)`,
`0 <= h <= 1`, equal `s` along an embedded arc `c(s)`. Suppose
`a in (A tensor K)_+` has `d_tau(a) = tau(h)` for all `tau in T(A)`, and let `a_n` be
finite-stage approximants with `[a_n]` increasing to `[a]` (for instance, finite-stage
approximants of `(a - 1/n)_+`). For all large `n`
there are stages `M` where `(a_n - eps)_+ <~ a_(n+1)` holds with `eps` below the
spectral gap of `a_n` at the diagonal point over `c(1)`. For every such `M`, the
rank of `a_(n+1)` at stage `M` is **not constant** on `Z x CP^(j_(M-1))`, where
`Z = {(x(s), x(1 - s)) : s in [0,1]}` and `x(s)` is the diagonal point of
`X_(M-1)` over `c(s)`. Every deep approximant must drop support somewhere along
the swap family and pick it up again.

**Model test.**
- *Untwisted tower.* With `alpha = beta = 0` no root is counted and the theorem
  says nothing. This is consistent with
  `untwisted-doubling-tower-has-a-nonconstant-continuous-rank`, whose realizer has
  constant rank `r_(M-1) - 2` along `Z`. The twisted version would need
  `m >= 2(r_(M-1) - 2)`, so exactly that realizer dies.
- *Trivial containments survive.* `phi(a') <~ phi(a')` meets the bound with
  equality, so the bound is not vacuous in the other direction.

**What it does not do.** It restricts approximants, not realizers. The drop loci
could still exist. The argument uses point traces of `A`, so it does not transfer
to `B` directly, because the point-evaluation blocks of `B` change the trace
bound `rank a_(n+1) <= r_M/2` on `Z`.

Proof: `toms-constant-rank-twisted-transport-proof`. Internal derivation, unreviewed.
