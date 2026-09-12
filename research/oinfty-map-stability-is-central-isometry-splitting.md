---
rg: 2
id: oinfty-map-stability-is-central-isometry-splitting
kind: claim
title: O-infinity-stability of a unital map is exactly central splitting by two isometries
---

Let `A` be separable and unital, `B` unital, and `phi:A->B` unital.  For a
finite set `F subset A`, define

```text
kappa_phi(F)
 = inf max_(a in F, r=1,2) ||[s_r,phi(a)]||,
```

where the infimum runs over pairs `s_1,s_2 in B` satisfying

```text
s_r^*s_t=delta_(r,t)1_B.
```

(The infimum is infinity if no such pair exists.)  Then the following are
equivalent:

1. `phi` is O-infinity-stable;
2. `kappa_phi(F)=0` for every finite `F subset A`;
3. the unit of `B_infinity intersect phi(A)'` is properly infinite.

The same criterion holds with a free-ultrafilter sequence algebra `B_omega`.
