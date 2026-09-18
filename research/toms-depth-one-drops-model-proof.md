---
rg: 2
id: toms-depth-one-drops-model-proof
kind: route
title: Pair each coordinate's L_2 slot with the mirror coordinate's L_1 slot and rotate through a vanishing section of Hom(L_2, L_1) in disjoint windows
target: toms-chern-swap-count-allows-depth-one-drops
requires: []
---

Notation is from the target. Let `sigma_(i) = R + 1 - i`, and put
`W_i = [c_i - eta, c_i + eta]`. Let `S in M_(n_1 x n_2)(C(CP^j))` represent `sigma`,
with `S = gamma_1 S gamma_2`.

**Step 1 (supports of P).**
- `g_i(s) > 0` iff `s > t_i`, so `rank a'(s) = #{i : t_i < s}`.
- The count `#{i in [1,R] : i < R s + 1/2 - R eta}` differs from `R s` by at most `5/8`.
- At `s = 0` no `g_i` is positive, and at `s = 1` all are, so the endpoint ranks are
  `(0, R)` and `(R, 0)`.
- The `L_2`-part of coordinate `i` in `P(s)` is `g_i(1-s) gamma_2`, positive iff
  `s < 1 - t_i = c_i - eta`.
- The `L_1`-part of coordinate `sigma_(i)` is `g_(sigma_(i))(s) gamma_1`, positive iff
  `s > t_(sigma_(i)) = c_i + eta`, since `t_(R+1-i) = 1 - (i - 1/2)/R + eta`.

So on `W_i` both slots of pair `i` carry nothing in `P`. The centers `c_i` are
`1/R` apart and `2 eta = 1/(4R)`, so the windows are disjoint.

**Step 2 (Q).** Write `C^(R(n_1 + n_2)) = ⊕_k (C^(n_1) ⊕ C^(n_2))` and call the summands
the slots `(k, L_1)` and `(k, L_2)`. For pair `i`, use the slots `(i, L_2)` and
`(sigma_(i), L_1)`. As `i` runs over `1..R` these exhaust all slots, and they are pairwise
disjoint.
- *Schedule.* Let `theta_i(s)` rise from `0` to `pi/2` on `[c_i - eta, c_i]` and
  `rho_i(s)` rise from `0` to `1` on `[c_i, c_i + eta]`. Both are continuous and
  constant outside.
- *Q.* Let `X_i(s, z)` map `C^(n_2)` to the two slots by
  `cos theta_i gamma_2 ⊕ sin theta_i S`, and put
  `Q^(i) = X_i X_i^* + rho_i gamma_1[(sigma_(i), L_1)]`, `Q = sum_i Q^(i)`.

`Q` is continuous and positive, and `Q^(i)` is supported on the slots of pair `i`.

**Step 3 (P <= Q).** `P` and `Q` are both block-diagonal over the pairs, so it suffices
to compare on each pair.
- For `s <= c_i - eta`, `Q^(i) = gamma_2` on `(i, L_2)`, which dominates
  `g_i(1-s) gamma_2 <= gamma_2`, and the `(sigma_(i), L_1)`-part of `P` vanishes.
- On `W_i` the pair carries nothing in `P`.
- For `s >= c_i + eta`, `Q^(i) = S S^* + gamma_1 >= gamma_1 >= g_(sigma_(i))(s) gamma_1` on
  `(sigma_(i), L_1)`, and the `(i, L_2)`-part of `P` vanishes.

**Step 4 (ranks).** Fix `(s, z)` and a pair `i`. `gamma_2(z)` has rank one, with unit
vector `v`.
- *`theta_i < pi/2`, `rho_i = 0`.* `X_i` restricted to `range gamma_2` is injective,
  because its `(i, L_2)` component is `cos theta_i v != 0`. Its kernel contains
  `ker gamma_2`, so `rank Q^(i) = 1`.
- *`theta_i = pi/2`, `rho_i = 0`.* `Q^(i) = S S^*`, of rank one iff `sigma(z) != 0`, and zero
  otherwise. This happens only at `s = c_i`.
- *`rho_i > 0`.* `Q^(i) = S S^* + rho_i gamma_1`. Its range lies in `range gamma_1(z)` and
  contains it, so the rank is one.

So `rank Q^(i)(s, z) = 1` except at `s = c_i`, `z in Z_sigma`, where it is `0`. The windows
are disjoint, so at most one pair has rank `0` at a time. Hence `rank Q in {R-1, R}`,
with drop set `{c_1..c_R} x Z_sigma`.

**Step 5 (hyperplane sections).** For `L_1 = O(-2) = range(z⊗z (z⊗z)^*/|z|^4)` and
`L_2 = O(-1) = range(z z^*/|z|^2)`, let `T(u ⊗ w) = u_0 w`. Then
`S = gamma_1 T^* gamma_2` sends `z/|z|` to `conj(z_0)/|z| · z⊗z/|z|^2`, which vanishes
exactly on `{z_0 = 0}`. Any `L_1 ⊗ L_2^* ≅ O(±1)` has a section, holomorphic or
antiholomorphic, vanishing exactly on a hyperplane.

**Step 6 (obstruction).** The drop-locus bound uses only
- the containments at the endpoint slices,
- `m`, and
- the Chern classes of the support bundle away from `D`.

The bands use only the ranks of `Q` on `K` and the endpoint ranks of the pushforward.
The model has
- containment `P <= Q`, the correct endpoint data `(0, R)` and `(R, 0)`, and the leaf
  profile within one rank;
- `m = R`, meeting the upper band `m <= R'` at `R = R'`;
- every rank `>= R - 1`, so any lower band with slack at least one rank holds.

On a point trace, a drop of one rank is `1/r_M` in `A`, and `beta_M/r_M` in `B`. So no
contradiction and no jump larger than one rank can be derived from these data on one
family. The firewall's jump is `K/2` top blocks. Square.
