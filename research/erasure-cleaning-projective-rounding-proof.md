---
rg: 2
id: erasure-cleaning-projective-rounding-proof
kind: route
title: Localize every cocycle row, cover its remaining edges, and classically decode the commuting tuple
target: erasure-cleaning-rounds-all-projective-parity-valleys
requires: []
---

For every good parity row `h_a` and every `j`, scalar centrality of the
commutators gives

```text
0=sum_i h_a(i)B(i,j).                                    (ECR1)
```

Thus every row of `B` belongs to the left side of `(ECP1)`.  Write

```text
b_i=c_i+s_i,  c_i in C,  supp(s_i) subset S=S(E).         (ECR2)
```

Let `T={i:c_i!=0}`.  If `eta` is small enough that `|S|<=delta L/2`, then
every `i in T` has

```text
wt(b_i)>=delta L-|S|>=delta L/2.
```

Since `sum_i wt(b_i)=beta L^2`,

```text
|T|/L <= 2 beta/delta.                                   (ECR3)
```

Put `R=S union T`.  If `i,j` both lie outside `R`, then `c_i=0` and
`b_i=s_i` is supported inside `S`, so `B(i,j)=0`.  Therefore `R` is a
vertex cover of the entire anticommutation graph and

```text
|R|/L <= K eta+2 beta/delta.                             (ECR4)
```

Replace `Q_i` by `I` for `i in R`.  The resulting tuple commutes, and this
first correction costs at most `4|R|/L`.  It can spoil only the checks in
`E` or checks incident to `R`; bounded column degree makes their fraction
`O(eta+|R|/L)`.

Simultaneously diagonalize the commuting corrected tuple.  On every joint
character atom its binary label violates only those spoiled checks.
Classical soundness moves that label to a codeword in `C` through at most
`O((eta+|R|/L)L)` coordinates.  Perform this nearest-codeword replacement
separately on the joint atoms.  The resulting joint PVM is supported on
`C`, so its coordinate marginals commute and satisfy every parity exactly;
the second average squared-HS cost is `O(eta+|R|/L)`.  Combining the two
corrections with `(ECR4)` proves `(ECP3)`.  Central direct sums follow by
performing the construction on each sign sector and integrating the same
uniform estimate.

