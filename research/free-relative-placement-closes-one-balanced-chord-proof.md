---
rg: 2
id: free-relative-placement-closes-one-balanced-chord-proof
kind: route
title: Couple the plus and minus conditional tables by two integer transports
target: free-relative-placement-closes-one-balanced-chord
requires: []
---

For each `epsilon`, `(FRP2)` says that the two nonnegative integer vectors
`(r_(0,s)^epsilon)_s` and `(r_(1,t)^epsilon)_t` have the same total.
A nonnegative integer matrix with those row and column sums exists: repeatedly
put the smaller of the first remaining row and column demands in their cell,
delete whichever demand is exhausted, and continue.  Denote the resulting
matrix by `n^epsilon`.

On the basis `(FRP4)`, define the `A_0` atom `e_(0,s)` to be the span of all
coordinates with first label `s`, and define `e_(1,t)` analogously from the
second label.  These two diagonal partitions commute.  Let `Z` act by the
sign `epsilon`.  Then

```text
rank(e_(0,s)(1+epsilon Z)/2)=sum_t n_(s,t)^epsilon
                            =r_(0,s)^epsilon,
rank(e_(1,t)(1+epsilon Z)/2)=sum_s n_(s,t)^epsilon
                            =r_(1,t)^epsilon.            (FRP7)
```

Simultaneous diagonalization of each original commuting pair `(A_i,X_i)`
labels its coordinates by `(s,epsilon)` with exactly the multiplicities in
`(FRP1)`.  Equation `(FRP7)` therefore supplies a coordinate bijection from
each original packet to `Omega`; its permutation unitary embeds the pair and
sends `X_i` to `Z`.  This proves `(FRP3)`.

The diagonal sign group `(C_2)^D` contains every separator sign and `Z`, and
the permutation group `S_D` contains both coordinate bijections.  Its natural
signed-permutation representation is irreducible, so its primitive central
idempotent cuts out the full `M_D(C)` block containing all the displayed
data.  Finally, when the relative placement has already been fixed, its joint
cell dimensions cannot be redefined by `(FRP5)`; the two sign transports must
partition the existing cells, which is exactly `(FRP6)`.  This identifies the
first fixed-cycle equation.
