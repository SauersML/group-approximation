---
rg: 2
id: atomic-leavitt-gap-on-nonzero-matrix-corner-proof
kind: route
title: Normalize the ordinary trace on the active corner and use cyclicity
target: atomic-leavitt-gap-on-nonzero-matrix-corner
requires: []
---

Put `r=rank(p)>0` and use the normalized corner trace

```text
tau_p(x)=Tr(x)/r,                  x in pM_d(C)p.
```

For every `i`, operator norm controls every tracial state, so

```text
|tau_p(t_i s_i)-1| <= ||t_i s_i-p||_op.               (AGP1)
```

Cyclicity gives `tau_p(s_i t_i)=tau_p(t_i s_i)`.  Hence

```text
|tau_p(sum_i s_i t_i)-m|
 <= sum_i ||t_i s_i-p||_op.                            (AGP2)
```

The completeness row gives

```text
|tau_p(sum_i s_i t_i)-1|
 <= ||sum_i s_i t_i-p||_op.                            (AGP3)
```

The triangle inequality between the scalars `m` and `1` proves `(ALG1)`.
If every summand is at most `epsilon`, there are `m+1` summands and `(ALG2)`
follows.

For the corona consequence, lift a nonzero corona projection to projections
`p_n`.  It is nonzero on an infinite subsequence.  Uniformly bounded lifts
of a hypothetical exact corner Leavitt family, compressed by `p_n`, have all
defects tending to zero.  Applying `(ALG2)` at every nonzero coordinate is a
contradiction.

