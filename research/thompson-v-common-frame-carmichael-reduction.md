---
rg: 2
id: thompson-v-common-frame-carmichael-reduction
kind: route
title: Align each common-pivot pair in one frame and charge only two disjoint centralizers
target: thompson-v-r5-coherent-carmichael-family
requires:
  - thompson-v-r5-uniform-common-pivot-centralizers
---

Let `A_0` be the fixed R1-area of the local `S_4` consequence

```text
(b_0 b_1)^2=1,
b_0=(p q c_0),       b_1=(p q c_1).
```

This is a constant because all four leaves are fixed in one shallow chart.
For `i>=2` put

```text
k_i=(c_0 c_i),       u_i=k_i b_0 k_i^(-1),
k_1=(c_0 c_1).
```

Every `u_i` is a literal conjugate of the one fixed word `b_0`, and `u_i^3`
is a conjugate of the fixed cube relator.  For `i!=j`, use the common frame

```text
l_(ij)=(c_0 c_i)(c_1 c_j).
```

Direct permutation multiplication gives

```text
k_i^(-1) l_(ij)       =(c_1 c_j)=s_(ij),
k_j^(-1) l_(ij) k_1   =(c_1 c_i c_j)=t_(ij).             (1)
```

Both right sides fix `p,q,c_0`, hence centralize `b_0`.  The two `(UCP)`
certificates therefore give equality loops of area at most `C` between

```text
u_i  and  l_(ij) b_0 l_(ij)^(-1),
u_j  and  l_(ij) b_1 l_(ij)^(-1).                         (2)
```

Replacing the four occurrences in `(u_i u_j)^2` by the common-frame words in
`(2)` costs at most `4C` relator cells.  What remains is the conjugate

```text
l_(ij) (b_0 b_1)^2 l_(ij)^(-1),
```

which costs `A_0`.  Consequently

```text
Area_(R1--R5)((u_i u_j)^2)<=4C+A_0                       (3)
```

uniformly in `M,i,j`.  Applying
`bounded-area-high-chromatic-conjugacy-collapse` to the complete graphs gives

```text
||U(b_0)-I||_2 <= 2(4C+A_0) def_R(U).                     (4)
```

Since `b_0` is a fixed conjugate of the Bleak--Quick generator
`b=(01 10 11)`, this proves the requested coherent Carmichael family and its
one-word ceiling.

