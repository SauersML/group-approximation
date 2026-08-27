---
rg: 2
id: repeated-ldpc-weyl-kernel-has-growing-approximate-rank
kind: claim
title: The repeated-LDPC Weyl kernel has logarithmically growing approximate rank
distinct_from:
  bounded-prefix-decision-cost-forces-bounded-approximate-rank: that bounds approximate rank for every bounded-expected-depth prefix predicate; this proves the required robust-rank lower bound for the actual repeated-code pairing kernel
  lin-code-space-pauli-test-has-only-logarithmic-weyl-rank: that upper-bounds the exact Weyl rank in one literal Justesen code-space test; this lower-bounds rank even after a fixed positive fraction of arbitrary entry changes
  repeated-good-ldpc-coordinates-give-private-weyl-sampler: that proves the sampled matrix-dimension gap and bounded occurrence; this audits the full cross-pairing matrix behind those coordinate lists
---

Let

```text
A=(a_i)_(i=1)^L,       B=(b_j)_(j=1)^L,
a_i,b_j in F_2^r,
```

be two spanning coordinate-functional lists.  Assume `L<=C r` and that the
linear code

```text
x |-> (a_i dot x)_(i=1)^L                              (LRK1)
```

has relative distance at least `delta>0`.  Repeat every coordinate of both
lists `R` times, put `N=LR`, and form the full repeated Weyl-sign matrix

```text
K_((i,u),(j,v))=a_i dot b_j,
1<=u,v<=R.                                               (LRK2)
```

Then every Boolean `N by N` matrix `K'` of rank at most `k` satisfies

```text
dist_H(K,K')/N^2
 >= (delta/(2L))(q-2^k),                                 (LRK3)
```

where `q` is the number of distinct vectors among the `b_j`.  Since `B`
spans, `q>=r`.  Consequently, whenever

```text
epsilon < delta/(4C),
dist_H(K,K') <= epsilon N^2,
```

one has

```text
rank_(F_2)(K') >= log_2(r)-1.                            (LRK4)
```

Thus the private repeated-code Weyl table has genuinely unbounded
approximate rank at every sufficiently small fixed error rate.  Quadratic
repetition and duplicate coordinate functionals do not dilute this fact.

Combining `(LRK4)` with
`bounded-prefix-decision-cost-forces-bounded-approximate-rank` gives a sharp
sanity gate.  Any deterministic synchronous-prefix procedure which computes
`(LRK2)` under the uniform pair distribution must have

```text
E depth = Omega(log log r).                              (LRK5)
```

If its second moment is used instead, then

```text
E(depth^2)=Omega((log log r)^2).                         (LRK6)
```

The truncation proof applies verbatim to any fixed binary addresses for the
`N` labels: after depth `m` there are at most `2^m` row-prefix classes.
Therefore a bounded-expected-prefix classical mechanism cannot certify or
generate the full Weyl pairing table used to justify the sampler's robust
rank.  This does **not** refute the same-basis decoder itself, which need not
compute untested cross signs.  It proves that a successful combined route
must use genuinely global code/operator structure rather than justify its
rank through a uniformly bounded expected amount of label information.
