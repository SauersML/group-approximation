---
rg: 2
id: left-orderable-non-sofic-via-integer-lamp-rigid-pair
kind: route
title: An integer-lamp wreath over a left-orderable rigid pair is left-orderable and nonsofic
target: left-orderable-non-sofic-group
requires: [left-orderable-group-with-rigid-compression-pair, sofic-groups-kill-rigid-compression-defects]
---

Let `Gamma <= G` be a pair as in `left-orderable-group-with-rigid-compression-pair`:
`G` left-orderable, `Gamma` and `G` Kazhdan, `Gamma` infranormal and not normal
in `G`.  Put `X = G/Gamma` with base point `o = Gamma`, and

```text
W = (direct_sum_(x in X) Z) x| G,        e_x = the generator of the lamp at x,
g e_x g^-1 = e_(g x).
```

**1. `W` is left-orderable.**  The kernel `L = direct_sum_X Z` is torsion-free
abelian, hence left-orderable, and `W/L = G` is left-orderable.  An extension
of a left-orderable group by a left-orderable group is left-orderable: fix
positive cones `P_L` and `P_G`, and declare `w` positive when its image in `G`
lies in `P_G`, or its image is trivial and `w in P_L`.  This set is a
semigroup, and `W` is the disjoint union of it, its inverse and `{1}`.  The same
extension argument shows that `W` is torsion-free.  It is locally indicable,
or has unique products, whenever `G` does.

**2. `W` carries a nontrivial rigid compression defect.**

- *A strict compressor exists.*  If every `g in P_Gamma` normalized `Gamma`,
  then `G = <P_Gamma>` would normalize `Gamma`.  So some `t in P_Gamma` has
  `t Gamma t^-1 < Gamma` strictly.  Pick `gamma in Gamma` outside
  `t Gamma t^-1`.
- *The root lamp centralizes `Gamma`.*  `gamma' o = o` for `gamma' in Gamma`,
  so `gamma' e_o gamma'^-1 = e_o`.  So `z = e_o` lies in `C_W(Gamma)`.
- *Its conjugate does not.*  `t e_o t^-1 = e_(t o)` and
  `gamma e_(t o) gamma^-1 = e_(gamma t o)`.  In additive notation
  `[t z t^-1, gamma] = e_(t o) - e_(gamma t o)`.  This is nonzero, because
  `gamma t Gamma = t Gamma` would put `gamma` in `t Gamma t^-1`.

**3. `W` is not sofic.**  `Gamma <= G <= W` with `Gamma` and `G` Kazhdan and
`Gamma` infranormal in `G`, and the defect `[t z t^-1, gamma]` is nontrivial.
`sofic-groups-kill-rigid-compression-defects` says a sofic group has no such
defect.  So `W` is left-orderable and nonsofic.  ∎

**Remarks.**

- This is the computation of `kun-thom-wreath-carries-rigid-defect` with the
  lamp group `Z/2` replaced by `Z`.  The lamp group plays no role in the defect.
  The change matters here because it removes the only torsion in the
  construction.
- The group double gives a second output.  The fold map `G *_Gamma G -> G` is
  injective on every conjugate of either factor.  So its kernel acts freely on
  the Bass--Serre tree and is free.  A free-by-left-orderable group is
  left-orderable, so `G *_Gamma G` is left-orderable, and it is nonsofic by
  `kt-pair-group-double-is-nonsofic`.
- Converse direction: the input pair contains the infinite Kazhdan group
  `Gamma`.  So this route cannot fire before Navas's Question 3 has a positive
  answer (`infinite-left-orderable-kazhdan-group-from-rigid-pair`).
