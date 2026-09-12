---
rg: 2
id: stw77-af-range-central-splitting-proof
kind: route
title: Split minimal projections and transport the splittings through matrix units
target: stw77-af-range-maps-are-oinfty-stable
requires: []
---

## Proof

First let `C subset B` be finite dimensional and unital.  Write

```text
C = direct_sum_(j=1)^q M_(n_j)
```

and choose matrix units `e^(j)_(ab)`.  Each `p_j=e^(j)_(11)` is a nonzero
positive element of `C`, hence is a properly infinite projection in `B`.
There are `v_(j,1),v_(j,2) in p_j B p_j` such that

```text
v_(j,r)^*v_(j,t)=delta_(r,t)p_j.
```

For `r=1,2` put

```text
s_(j,r)=sum_(a=1)^(n_j) e^(j)_(a1) v_(j,r) e^(j)_(1a),
s_r=sum_(j=1)^q s_(j,r).
```

Matrix-unit multiplication gives

```text
s_(j,r)e^(j)_(ab)=e^(j)_(ab)s_(j,r),
s_(j,r)^*s_(j,t)=delta_(r,t)1_(M_(n_j)).
```

Different summands have orthogonal central supports.  Therefore
`s_r^*s_t=delta_(r,t)1_B` and both `s_r` commute with all of `C`.

Now let the range be AF.  For an arbitrary finite subset of `C` and
`epsilon>0`, choose a unital finite-dimensional subalgebra approximating it
within `epsilon/4`.  The construction above gives exact orthogonal isometries
commuting with that subalgebra, hence commuting with the original finite set
within `epsilon`.  Thus every finite-set defect `kappa_phi(F)` from
`oinfty-map-stability-is-central-isometry-splitting` vanishes.  That criterion
proves O-infinity-stability.
