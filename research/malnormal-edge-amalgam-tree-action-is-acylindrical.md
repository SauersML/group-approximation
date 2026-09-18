---
rg: 2
id: malnormal-edge-amalgam-tree-action-is-acylindrical
kind: claim
title: An amalgam whose edge group is malnormal in one factor acts acylindrically and non-elementarily on its Bass--Serre tree
distinct_from:
  fpbs-minasyan-osin-weakly-malnormal-splittings: that imports the Minasyan--Osin theorem for weakly malnormal edge groups, whose proof runs through WPD elements and hyperbolically embedded subgroups; this assumes the stronger one-sided malnormality and proves acylindricity of the tree action itself by an elementary counting argument, with no import.
  two-generated-acylindrical-normal-generation-upgrade: that is a construction consuming an acylindricity theorem; this is the acylindricity theorem.
artifacts:
  - research/malnormal-edge-amalgam-tree-action-is-acylindrical-proof.md
---

**Claim.**  Let `G = A *_C B`.  Suppose that `C` is malnormal in `B`
(`C cap bCb^{-1} = 1` for every `b in B \ C`), that `C != B`, and that some
`t in A` satisfies `t notin C` and `t^2 notin C`.  Let `T` be the Bass--Serre
tree of the splitting.  Then:

1. **(S3)** every geodesic edge path of length `3` in `T` has trivial pointwise
   stabilizer;
2. **(ACYL)** the action of `G` on `T` is acylindrical in Bowditch's sense.
   For vertices this reads: if `d(x,y) >= 2ε+5`, then at most `4ε+2` elements
   `g` satisfy `d(x,gx) <= ε` and `d(y,gy) <= ε`;
3. **(NE)** for any `b in B \ C`, the elements `tb` and `bt` are loxodromic
   with translation length `2` and no common fixed point at infinity.

Hence the action is non-elementary.  `G` is acylindrically hyperbolic in
Osin's defining sense: it admits a non-elementary acylindrical action on a
hyperbolic space.

The proof is self-contained: Bass--Serre theory for one edge, free reduction
in trees, and the normal form theorem for amalgams.  It is the
internal replacement for Minasyan--Osin in
`two-generated-acylindrical-upgrade-without-minasyan-osin`.
