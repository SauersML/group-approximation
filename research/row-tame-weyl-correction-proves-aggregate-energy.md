---
rg: 2
id: row-tame-weyl-correction-proves-aggregate-energy
kind: route
title: Price the selected Weyl correction by the two endpoint row values
target: iwahori-cubics-control-aggregate-weighted-bs-orbit-energy
requires:
  - iwahori-weyl-coboundary-admits-row-tame-target
  - same-core-involution-cubic-gauge-coercivity
---

Choose `c` and `X_0` from `(RCT2)--(RCT4)`.  The input endpoint `X` and the
corrected endpoint `X_0` both have `O(delta)` involution and first-cubic
defect, while

```text
X=cX_0,        [c,T]=0.
```

Apply the exact pairwise estimate `(SCG2)` to obtain

```text
||c-1||_2<=C delta.                                    (1)
```

Equation `(RCT2)` says that this very gauge absorbs the complete regular
Weyl coboundary; the only leftover is the separately allowed
`O(delta)` fixed/holonomy component.  Hence `(1)` is precisely the
gauge-optimized formulation declared equivalent to `(IAG1)` in the target
claim.  No Taylor estimate, spectral summation, or path integral enters.

