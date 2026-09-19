---
rg: 2
id: paired-frame-moving-kernel-is-a-rank-one-veronese-clock-proof
kind: route
title: Split the exterior square and follow the projective slope orbit
target: paired-frame-moving-kernel-is-a-rank-one-veronese-clock
requires:
  - alternating-free-ring-shears-have-strict-degree-drift
  - support-packet-paired-word-frame-exposes-forbidden-rank
artifacts:
  - experiments/paired_frame_moving_kernel_orbit.py
---

The binary kernel calculation gives `(MVK2)`.  Split
`R^4=R^2 direct_sum R^2` along coordinates `(0,1)` and `(2,3)`.  The two
exterior-square lines `R e_01` and `R e_23` are fixed because `det S=1`.
The remaining generator is `e_13`, the tensor of the second basis vectors in
the two blocks.  Applying `S^n` to both factors gives `(MVK4)`, proving
`(MVK3)`.

The strict-degree theorem gives

```text
deg c_n=2n-1,        deg d_n=2n-2
```

with leading coefficient one.  Squaring doubles degrees in `F_2[x]` and the
mixed product adds them, proving `(MVK5)` without cancellation.

After dividing `(MVK4)` by `d_n^2` over `F_2(x)`, the moving line is the
Veronese point

```text
[r_n^2:r_n:r_n:1],       r_n=c_n/d_n.                  (MVK7)
```

If `L_n=L_m`, then `(MVK7)` gives `r_n=r_m`.  The projective action of `S` is
invertible, so for `n>m` this would imply `r_(n-m)=r_0=0`.  But
`deg c_(n-m)=2(n-m)-1`, so `c_(n-m)` is nonzero, a contradiction.  Hence the
lines are pairwise distinct.  They lie in a complement of `K_fixed`, which
proves `(MVK6)`.

The verifier independently computes polynomial Gaussian ranks over the exact
fraction field `F_2(x)`.  Through 48 levels it asserts all 1128 pairwise
intersection dimensions equal two, the degree formula, and total orbit-span
rank five.  These checks guard the closed-form proof against convention or
wedge-coordinate errors.
