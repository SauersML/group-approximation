---
rg: 2
id: periodic-higman-bs-clocks-have-three-opnorm-small-seams
kind: claim
title: Periodic Higman clocks make three occurrence seams operator-norm small
artifacts:
  - research/periodic-higman-bs-clocks-have-three-opnorm-small-seams-proof.md
distinct_from:
  three-higman-bs-seams-vanish-fourth-is-product-holonomy: that uses normalized Hilbert--Schmidt spectral transport for general asymptotically Haar periodic clocks; this gives an explicit q=3^n family with a quantitative operator-norm bottleneck matching bound.
  split-higman-cycle-has-haar-marginals-and-maximal-role-gap: that keeps all four occurrence seams asymptotically maximal; this chooses gauges making any prescribed three seams tend to zero in operator norm while retaining an exactly maximal marked distance.
  higman-hs-microstates-are-near-glued-exact-bs-cycles: that uses Hilbert--Schmidt stability of BS(1,2) to reduce actual Higman microstates to a four-seam gluing problem; this is an operator-norm countermodel for every proper-subcycle gluing argument and makes no operator-norm stability assertion.
---

**ESTABLISHED.**  Put `q_n=3^n`.  On the standard basis indexed by
`Z/q_n Z`, let

```text
D_n e_x = exp(2 pi i x/q_n)e_x,
P_n e_x = e_(2^(-1)x).
```

Then

```text
P_n D_n P_n^(-1)=D_n^2.                              (HOC1)
```

There is a unitary `H_n` such that

```text
||D_n-H_n P_n H_n^*||_op
  <= 2 pi (n+2)/3^n -> 0.                            (HOC2)
```

Gauge four copies of the exact packet `(P_n,D_n)` by

```text
G_(j,n)=H_n^j,                 j=0,1,2,3.
```

For three consecutive repeated-generator interfaces, the target occurrence
from one packet and the conjugator occurrence from the next differ by at most
the right side of `(HOC2)` in operator norm.  Nevertheless every conjugator
occurrence remains maximally visible:

```text
||G_(j,n) P_n G_(j,n)^* - 1||_op=2.                  (HOC3)
```

The fourth cyclic seam is the only unpaid term.  In the homogeneous gauge it
is bounded by the matching error plus the order-four return

```text
||H_n^4 P_n H_n^(-4)-P_n||_op.                       (HOC4)
```

Thus exact local `BS(1,2)` packet relations, operator-norm spectral matching,
and any proper subcycle of the Higman square cannot prove point-norm collapse
of Higman's generators.  The missing statement is genuinely the fourfold
occurrence holonomy.  This does **not** construct an operator-norm Higman
microstate: the fourth seam in `(HOC4)` is precisely what remains open.

## Consequence for the torsion-free non-MF route

Higman's group is torsion-free, finitely presented, and every exact
finite-dimensional representation is trivial.  To turn that sterility into
MF collapse one still needs point-norm stability at a nontrivial generator.
The present family proves that such stability cannot be obtained by
exactifying or classifying the four `BS(1,2)` edges separately and checking
fewer than all four occurrence identifications.  A valid proof must control
the ordered four-matcher return in operator norm; local packet stability is
not the missing theorem.
