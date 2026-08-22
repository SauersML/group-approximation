---
rg: 2
id: bounded-prefix-approximate-rank-proof
kind: route
title: Truncate the stopping tree and count its prefix rows
target: bounded-prefix-decision-cost-forces-bounded-approximate-rank
requires:
  - dense-offdiagonal-leavitt-heisenberg-packet
---

Fix `k`.  Truncate the prefix procedure after `k` steps and output zero on
the leaves which have not yet stopped.  Because this is a genuine stopping
procedure, whether it has stopped and its output are determined by the two
length-`k` prefixes.  The resulting matrix `K'_(n,k)` is therefore constant
on every rectangle

```text
{u:u|_k=a} x {v:v|_k=b}.
```

It has at most `2^k` distinct rows, so its rank over `F_2` is at most
`2^k`.  It differs from `K_n` only where `L_n>k`.  Markov's inequality gives

```text
Pr(L_n>k) <= C/k.
```

Taking `k=ceil(C/epsilon)` proves `(BPD2)` (enlarging `k` harmlessly if
needed).  Under the second-moment hypothesis,

```text
Pr(L_n>k) <= C_2/k^2,
```

and `k=ceil(sqrt(C_2/epsilon))` gives the stated improvement.

For a Weyl table, changing the exceptional entries produces exactly the
kind of average-relation model which a constant-soundness argument must
exclude.  If every such small edit retained rank tending to infinity, it
would contradict the dimension-independent rank bound above.  Thus bounded
expected stopping depth and robust growing pairing rank cannot coexist.

