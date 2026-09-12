---
rg: 2
id: cyclic-doubling-matching-proof
kind: route
title: Match every even root exactly and every odd root to its nearest even neighbor
target: cyclic-doubling-matching-hides-full-deep-root-budget
requires: []
---

The eigenvalue multiset of `P_N` consists of every `m`-th root once. The
multiset of `P_N^2` consists of every even power `zeta^(2k)` twice. Match
the source eigenvalue `zeta^(2k)` to one copy of the identical target and
match `zeta^(2k+1)` to the second copy of `zeta^(2k)`. This bijection is
implemented by a permutation unitary and has normalized squared cost

```text
(1/m)(m/2)|zeta-1|^2
 =2 sin^2(pi/m),                                        (CDP1)
```

which is `(CDM2)` because `m=2^N`.

It is optimal: every odd source root is at chordal distance at least
`|zeta-1|` from every even target root, while every even source contributes
a nonnegative cost. There are `m/2` odd roots, giving `(CDP1)` as a lower
bound for every matching.

Exactly two eigenvalues of `P_N`, namely `1` and `-1`, lie in `E_<=1`.
This proves `(CDM3)`. Since the left side of `(CDM4)` tends to one while
the right-hand infimum in `(CDM2)` tends to zero, no depth-independent `C`
exists.

