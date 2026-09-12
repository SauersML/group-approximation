---
rg: 2
id: same-reservoir-weyl-doubling-gap-proof
kind: route
title: Compare the half-period commutator before and after simultaneous doubling
target: same-reservoir-weyl-pair-has-fixed-depth-doubling-gap
requires: []
---

Centrality of `Z=[P,Q]` gives, for every integer `k`,

```text
[P,Q^k]=Z^k,       [P^k,Q]=Z^k.                         (SWP1)
```

By `(SWD1)`, `Z^m=-I`. Conjugating the first identity by `V` gives

```text
[V P V^*,(V Q V^*)^m]=-I.                               (SWP2)
```

The proposed doubled targets instead satisfy

```text
[P^2,(Q^2)^m]=Z^(4m)=I.                                 (SWP3)
```

For unitary pairs `(A,B)` and `(A',B')`, telescoping the four-letter
commutator word gives

```text
||[A,B]-[A',B']||_2
 <=2||A-A'||_2+2||B-B'||_2.                             (SWP4)
```

Moreover power telescoping gives

```text
||(V Q V^*)^m-(Q^2)^m||_2<=m epsilon_Q.                 (SWP5)
```

The normalized Hilbert--Schmidt distance from `-I` to `I` is two.
Applying `(SWP4)--(SWP5)` to `(SWP2)--(SWP3)` yields

```text
2<=2 epsilon_P+2m epsilon_Q,
```

which is the first inequality in `(SWD3)`.

Interchanging `P` and `Q`, use

```text
[(V P V^*)^m,V Q V^*]=-I,
[(P^2)^m,Q^2]=[P^d,Q^2]=I
```

to obtain the second inequality. Adding them proves the first part of
`(SWD4)`. Finally `x^2+y^2>=(x+y)^2/2` proves the squared estimate.
