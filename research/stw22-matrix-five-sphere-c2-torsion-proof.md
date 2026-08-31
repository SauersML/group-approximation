---
rg: 2
id: stw22-matrix-five-sphere-c2-torsion-proof
kind: route
title: Cancel c1 and c2 on the carrier skeleton and absorb the unstable rank-two pi5 class
target: stw22-matrix-weighted-copy-codim3-uniform-s5-fillings
requires:
  - stw22-matrix-weighted-copy-codimension-two-uniform-s4-fillings
artifacts:
  - research/artifacts/stw22-dim6-factor-bundle-breakthrough-2026-08-31.md
---

Let `q` have rank `k` and target codimension `c>=3`.  Then
`St_n(q)=U(n)/U(c)` is `2c`-connected, hence five-connected.

For a small `S^5` centred at `q`, triangulate finely and let every vertex
hard carrier have rank at most

```text
K=floor(4n delta^2/kappa^2).
```

If `K=0`, direct rotation fills.  If `K>0` and `k<=6K+2`, arbitrary
fiveconnectivity and the Stiefel diameter give radius below
`12delta/kappa`.  Otherwise construct a rank `6K` carrier over the
barycentric two-skeleton, containing the join attached to the least face.
Its complement has rank at least three.  Split off its determinant line and
promote it into the carrier, killing `c_1`; extend over the three- and
four-skeleta, using detection of `pi_2` by `c_1` and vanishing of `pi_3`.

Over the resulting four-skeleton, the complement has rank at least two.
A complex rank-`r` bundle over a four-dimensional CW complex has `r-2`
independent sections: the successive unit-sphere fibres are at least
four-connected.  Hence the complement is `D plus trivial`, with `D` rank
two.  Promote `D` into the carrier.  Since the total source bundle is
trivial and `c_1` already vanishes, Whitney's formula gives

```text
c_1(E+D)=c_2(E+D)=0.                                  (M5-1)
```

On each top five-cell boundary, the carrier lies in a Grassmannian
containing the local vertex carrier.  Its `pi_4` is either zero or `Z`
detected by tautological `c_2`; `(M5-1)` makes the boundary null.  Thus a
global carrier exists on `S^5`, has rank at most `6K+3`, and captures the
operator-norm defect.

After direct rotation, localized pairs with carrier rank `R` form a bundle
`Z_R` over `Gr_R(C^k)` with fibre `V_R(C^(R+c))`.  Since `c>=3`, the fibre
has zero `pi_4,pi_5`, so `pi_5(Z_R)=pi_5(Gr_R(C^k))`.  As `R>=3`, the
unitary exact sequence shows this base group is zero except when the source
complement has rank two, where it is `Z/2` coming from `pi_4(U(2))`.
In that exceptional case promote the entire rank-two complement into both
carrier and partial isometry; the represented frame is unchanged and the
new base is a point.  The final carrier rank is at most

```text
6K+5<=11K.
```

Every localized filling is therefore within `14delta/kappa` of `q`.
Taking `kappa=epsilon_0/40`, `delta=epsilon_0^2/2560` proves the quadratic
projection modulus.  A high-low cut transfers it to arbitrary matrix
weights with the displayed cubic modulus; finite-dimensional polar
decomposition also gives global fiveconnectivity.

