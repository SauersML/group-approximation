---
rg: 2
id: sp4-maximal-parabolics-contain-no-isw-affine-subgroup
kind: claim
title: Neither maximal parabolic of Sp4(Z) contains the Ioana--Spaas--Wiersma affine obstruction group
distinct_from:
  sp2g-z-full-c-star-algebra-has-llp: that is the global LLP question; this excludes the two canonical parabolic subgroup shortcuts but does not classify every subgroup of Sp4(Z).
  isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals: that computes why Theorem A cannot be rerun on the whole parabolic; this rules out importing Corollary B merely by subgroup permanence.
---

Let `F < SL_2(Z)` be any nonamenable free subgroup and put

```text
E = Z^2 rtimes F                                             (SPF1)
```

with the standard action.  Up to harmless finite-index and finite-kernel
changes, the two integral maximal parabolics of `Sp_4(Z)` are

```text
P_S = Sym^2(Z^2) rtimes GL_2(Z),
P_K = H_3(Z) rtimes SL_2(Z),                                 (SPF2)
```

where the Klingen Levi acts in the standard way on
`H_3(Z)/Z(H_3(Z)) = Z^2` and fixes the centre.  Neither `P_S` nor `P_K`
contains `E`.

This closes the most immediate subgroup attack on
`sp2g-z-full-c-star-algebra-has-llp`: Ioana--Spaas--Wiersma Corollary B
cannot be imported to `Sp_4(Z)` through its Siegel or Klingen parabolic.
It does not exclude an embedding elsewhere in `Sp_4(Z)`; doing that would
require a global classification of affine subgroups, not merely the
parabolic structure.
