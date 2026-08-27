---
rg: 2
id: bulk-amplification-outruns-recursive-copy-count
kind: route
title: Amplify the good bulk faster than any prescribed finite recursive test packet
target: word-recursion-cannot-amplify-sublinear-summands
requires: []
---

Normalized traces and squared HS norms are dimension-weighted direct-sum
averages, proving the fixed-depth identity immediately.

For the diagonal statement, fix one bad tuple `W`. Given `D_(L_n)`, first
choose a regular bulk microstate `V_n` accurate enough on every word used by
that finite packet that

```text
E_(L_n)(V_n)<=1/n.
```

Replace `V_n` by `K_n` identical copies and append `W`. Choose `K_n` so large
that

```text
N_(L_n) C_(L_n)^2 dim(W)/(K_n dim(V_n)+dim(W)) <= 1/n.
```

The resulting tuple has the same regular limiting character and defects as the
bulk, keeps `W` as an exact reducing summand, and has test energy at most
`2/n`. Since every evaluated word is block diagonal, no conjugacy orbit,
expander walk, or recursive self-copy can escape the reducing summand. Corner
renormalization detects `W` only after dividing by its trace, and multiplying
back into ambient HS energy restores the same vanishing factor.
