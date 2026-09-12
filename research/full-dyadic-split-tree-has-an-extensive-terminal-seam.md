---
rg: 2
id: full-dyadic-split-tree-has-an-extensive-terminal-seam
kind: claim
title: Splitting every dyadic child makes the finite-dimensional terminal seam extensive
distinct_from:
  consecutive-dyadic-splitting-does-not-report-dimension: that follows one consecutively halved block and sees only the two-adic valuation, with one rank-one seam of vanishing normalized mass; this follows every surviving child and proves the mutually orthogonal seams exhaust the whole matrix carrier.
  schur-flip-rank-is-residual-atomic-granularity: that identifies a depth-r exact Pauli factor with divisibility by 2^r; this gives the quantitative normalized-HS ledger when exact divisibility is replaced by orthogonal remainder projections at every node.
  adaptive-all-pairs-schur-replica-table-compiler: that asks a finite controller to synthesize and return the entire growing replica table; this is only the dimension-free rank/energy endpoint once a full split tree has been decoded.
---

ESTABLISHED.  Let `P_empty=I_k` and, for every binary word `v` of length
less than `R`, let

```text
P_(v0), P_(v1), E_v <= P_v
```

be pairwise orthogonal projections satisfying

```text
P_v=P_(v0)+P_(v1)+E_v,
rank(P_(v0))=rank(P_(v1)).                              (FDS1)
```

Then all remainder projections `E_v` and all depth-`R` leaf projections are
mutually orthogonal and

```text
I_k = directSum_(|v|<R) E_v
        directSum directSum_(|w|=R) P_w.                (FDS2)
```

Moreover every depth-`R` leaf has

```text
rank(P_w)<=floor(k/2^R).                                (FDS3)
```

Consequently, once `2^R>k`, every leaf is zero and

```text
sum_(|v|<R) tr_k(E_v)=1.                                (FDS4)
```

If the coverage defect at node `v` is measured by

```text
delta_v=||P_v-P_(v0)-P_(v1)||_(2,k),
```

then orthogonality gives `delta_v^2=tr_k(E_v)`, so `(FDS4)` is the exact
Pythagorean floor

```text
sum_(|v|<R) delta_v^2=1.                                (FDS5)
```

Thus rank-one terminal failures are dilutable only when one path is
inspected.  A full binary split tree cannot hide them: choosing a larger
matrix merely postpones the depth at which an order-one total seam appears.
The same statement holds on a carrier `P_empty` after normalizing by ambient
dimension, with right side `tr_k(P_empty)`.

This is the analytic mechanism the adaptive dyadic route should exploit.
It does not finitely groupify the tree.  A fixed presentation must still
address all active nodes, make their decoded domains orthogonal, and pack
their errors into one relator or one all-pairs table with no depth-dependent
union bound.  Finite cyclic truncations which identify different nodes do
not satisfy the orthogonality premise and remain the principal escape.

