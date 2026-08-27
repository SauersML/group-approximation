---
rg: 2
id: agent-free-compressor-contractive-toeplitz-no-go-proof
kind: route
title: Compare the two one-sided defects through contraction and trace
target: agent-free-compressor-contractive-toeplitz-no-go
requires: []
---

For contractions `X,Y`, put `delta=||YX-I||_2`. If `delta>=1`, the claimed
bound follows from `||I-XY||_2<=2`. Suppose `delta<1`. The triangle inequality and
`||YX||_2<=||X||_2` give `||X||_2>=1-delta`. Positivity and contractivity of
`X^*X` then give

```text
||I-X^*X||_2^2<=tr(I-X^*X)<=2 delta.
```

The same bound holds for `I-XX^*`. Cyclicity of trace and
`|tr(YX-I)|<=delta` give

```text
||Y-X^*||_2^2
 <=2-2 Re tr(YX)
 <=2 delta.
```

Finally

```text
||I-XY||_2
 <=||I-XX^*||_2+||X(X^*-Y)||_2
 <=2 sqrt(2 delta).
```

This is uniform in matrix dimension and proves the claim.
