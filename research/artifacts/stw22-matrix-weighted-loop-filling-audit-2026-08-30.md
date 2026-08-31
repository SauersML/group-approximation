# STW XXII: dimension-free matrix weighted-loop filling audit

## Result

For normalized matrix factors, all weighted orthogonal-copy fibres with a
strict unused range have one loop-filling modulus independent of matrix
size, copy number, the positive weight, and the size of the stated slack.
An explicit modulus is

```text
rho(epsilon)=min(epsilon,1)^3/276480.
```

The projection-frame core has the quadratic modulus
`min(epsilon,1)^2/2560`.

## Load-bearing checks

1. **No continuous eigenbasis is assumed.** On finitely many parameter
   arcs, hard spectral projections are chosen only at the arc centres.
   Each has rank at most `K`. Consecutive projections are placed inside a
   rank-`2K` carrier, and adjacent carriers are joined through the
   Grassmannian of rank-`2K` projections containing the one centre
   projection valid on that transition arc.
2. **All rank edge cases are covered.** If `K=0`, no carrier is needed. If
   `rank(q)<2K`, the entire Stiefel space has normalized `2`-diameter
   `O(delta/kappa)` and is simply connected. If `L=rank(q)`, the base
   Grassmannian in the defect bundle is a point.
3. **The defect bundle is simply connected.** Its base is
   `Gr_L(C^rank(q))`; its fibre is `V_L(C^(L+c))`, where
   `c=n-rank(q)>=1`. Both fundamental groups vanish, and the homotopy exact
   sequence of the locally trivial bundle kills the total fundamental
   group.
4. **The uncontrolled topological filling is metrically controlled.** Every
   localized defect frame differs from the base only on a rank-`L` right
   support. Therefore every point of any filling has normalized
   `2`-distance at most `2sqrt(L/n)`.
5. **Replication is isometric.** A polar `m`-frame is identified with one
   partial isometry having initial projection equal to the sum of the base
   range projections. The Hilbert-sum tuple metric equals its normalized
   `2`-metric exactly.
6. **The low spectral part costs no factor of `m`.** Its squared weighted
   displacement is at most `4m tau(ap_l)<=4eta`, because
   `m tau(supp(a))<=1`. Its relative extension exists since the remaining
   low-frame Stiefel fibre has at least one unused target dimension.

## Sharp boundary and trust limit

If the total support fills the whole matrix algebra, uniform loop filling
fails: `diag(z,1,...,1)` is an essential determinant loop in `U(n)` and has
normalized `2`-radius `2/sqrt(n)`. Conversely, the proof needs only one
unused matrix dimension, not a uniform trace-sized complement.

No diffuse-factor conclusion is recorded. The missing input there is a
continuous small-trace spectral-capture projection for `2`-norm-continuous
loops. The matrix proof obtains it from operator-norm continuity in fixed
dimension, an implication which is false uniformly and false in a
`II_1` factor.
