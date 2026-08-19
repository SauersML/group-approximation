---
rg: 2
id: atlas-a8-t21-diagonal-energy-envelope-proof
kind: route
title: Weighted Cauchy and its equality vector give the reciprocal envelope
target: atlas-a8-t21-diagonal-energy-envelope
requires: []
artifacts:
  - experiments/atlas_a8_four_cycle_raw_s3.py
---

Put

```text
l=(2,2,4),
x=(x_01,x_23,x_30),
C=diag(c_01,c_23,c_30).
```

The exact eight-letter word gives `a<=l.x`.  Weighted Cauchy says

```text
(l.x)^2
 = (C^(-1/2)l . C^(1/2)x)^2
 <= (l^T C^(-1) l) (x^T C x).
```

Now

```text
l^T C^(-1) l
 = 4/c_01 + 4/c_23 + 16/c_30.
```

Thus the reciprocal condition at most one proves the claimed diagonal bound.

It is also sharp.  Take

```text
x=C^(-1)l,
```

or any positive scalar multiple.  All three coordinates are nonnegative and
weighted Cauchy is an equality, so a diagonal form `x^T C x` can dominate
`(l.x)^2` for every such `x` only if `l^T C^(-1)l<=1`.

Finally, minimizing `max(c_01,c_23,c_30)` under the reciprocal constraint gives
`c_01=c_23=c_30=24`: if all three are at most `M`, then the reciprocal sum is
at least `24/M`, hence `M>=24`.  This certifies that the old symmetric constant
cannot be improved by merely retuning diagonal Cauchy; any further gain must
use anisotropy, several group identities, or genuinely non-diagonal
correlations.