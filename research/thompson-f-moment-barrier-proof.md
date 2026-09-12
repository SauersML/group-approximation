---
rg: 2
id: thompson-f-moment-barrier-proof
kind: route
title: Infinite spectrum puts the truncated moment vector in the interior, so an atom at 1 can be added
target: thompson-f-moment-data-cannot-certify-nonamenability
requires: []
---

Notation as in the target. `tau` is the canonical trace on the group von Neumann algebra
`L(F)`, and `mu(B) = tau(1_B(P))`.

**Step 1. `supp mu` is infinite.**
- `tau` is faithful, so every open set meeting `sigma(P)` has positive `mu`-measure. Hence
  `supp mu = sigma(P)`.
- Suppose `sigma(P) = {lambda_1, ..., lambda_k}` is finite. `P` is not a scalar (it moves
  `delta_e`), so `k >= 2`. Each spectral projection
  `E_i = prod_{j != i} (P - lambda_j)/(lambda_i - lambda_j)` is a polynomial in `P`, so it
  lies in `C[F]`, and `E_i(1 - E_i) = 0` with `E_i != 0, 1`.
- `F` is bi-orderable, being a group of orientation-preserving PL homeomorphisms of `[0,1]`:
  order by the sign of `f(x) - x` at the first point where `f` differs from the identity.
  Bi-orderable groups have unique products, so `C[F]` has no zero divisors, a contradiction.

**Step 2. Pass to `[0, 1]`.** Let `mu_2` be the image of `mu` under `t = x^2`. It is a
probability measure on `[0, ||P||^2]`, contained in `[0, 1]`, with moments `M_j`, and it has
infinite support.

**Step 3. The moment vector is interior.** The truncated moment space
`W_N = {(int t^j dnu)_{j=1..N} : nu a probability measure on [0,1]}` is the convex hull of the
moment curve `t -> (t, ..., t^N)`, `t in [0,1]`. It is compact and convex with nonempty
interior. Suppose `m = (M_1, ..., M_N)` lies on its boundary.
- A supporting hyperplane gives `c in R^N \ {0}` and `b` with `c . v >= b` on `W_N` and
  `c . m = b`.
- Taking `v` as the moment vector of `delta_t` makes `r(t) = sum_j c_j t^j - b` nonnegative on
  `[0,1]`.
- `int r dmu_2 = c . m - b = 0`, so `mu_2` is supported on the zero set of the nonzero
  polynomial `r`. That set is finite, contradicting Step 2.

So `m` is interior.

**Step 4. Add an atom at 1.** Let `u = (1, ..., 1)`, the moment vector of `delta_1`. For small
`eps > 0` the vector `m_eps = (m - eps u)/(1 - eps)` stays in the interior of `W_N`. Choose a
probability measure `nu'` on `[0,1]` representing `m_eps`, and set
`nu_2 = (1 - eps) nu' + eps delta_1`.
- `nu_2` has moments `m`, and `1 in supp nu_2`.
- Let `nu` be the symmetric measure on `[-1,1]` that splits the mass of `nu_2` at `t` equally
  between `+-sqrt(t)`. Its even moments are `M_j` for `j <= N`, its odd moments vanish, and
  `+-1 in supp nu`.

**Step 5. Conclusion.** A statement deduced from `c_0, ..., c_{2N}` alone holds for `nu`. Any
bound `||P|| <= s < 1` would put the support below `s`, but `nu` reaches 1. Kesten's theorem
identifies `||P|| < 1` with non-amenability.

The positive direction survives. If the monic orthogonal polynomial `p_k` of `mu_2` is
well-defined (Hankel positive definite up to size `k`) and `p_k(theta) < 0`, then
`||P||^2 > theta`.
- Let `x_k` be the largest zero of `p_k`, and `q = p_k/(x - x_k)`.
- Orthogonality gives `int (x - x_k) q^2 dmu_2 = int p_k q dmu_2 = 0`.
- If `supp mu_2 <= x_k` this forces `mu_2` onto the `k - 1` zeros of `q`, contradicting
  Hankel positivity. So `sup supp mu_2 >= x_k > theta`.

That is the certificate format used by `experiments/thompson-f/cogrowth_exact.py`.

**Trust surfaces.**
- Bi-orderability of `F` is classical (e.g. Clay–Rolfsen, *Ordered Groups and Topology*); it
  is quoted, not re-read.
- Kesten's criterion is classical.
- Everything else is proved above.
