---
rg: 2
id: sl3-raw-weyl-rectangle-pins-only-equal-rank-corners
kind: claim
title: The raw SL3 Weyl rectangle pins loop gauge only after equal-rank corner authentication
distinct_from:
  raw-denominator-incidence-kills-off-diagonal-shell-orbit: That compares the 42 raw branch projections and isolates decoded-to-raw distance; this computes one explicit simple-Weyl rectangle at the partial-isometry level and gives the exact equal-rank authentication formula.
  three-chart-loop-retains-free-multiplicity-holonomy: That leaves the edge transports abstract and finds arbitrary loop gauge; this inserts the literal denominator section words and proves that their raw relative loop is pinned.
  balanced-raw-lamp-orbit-cannot-approximate-shell-pvm: That gives the aggregate rank-mismatch floor; this identifies source-fullness as the exact place where that rank mismatch blocks transfer of the pinned loop to a decoded atom.
---

# The raw SL3 Weyl rectangle pins only equal-rank decoded corners

Put

```text
C=SL_3(Z),       h=diag(2,1,1/2),
```

and let `w_1=s_12`, `w_2=s_23` be signed simple Weyl representatives in
`C`.  Write

```text
h_w=w h w^(-1).                                         (RWR1)
```

This is the base branch of the 42-section identity: the two section words

```text
a_w=h_w,       b_w=w h,       d_w=w^(-1)                (RWR2)
```

satisfy `a_w=b_wd_w`.

Let `rho` be an exact unitary representation of these words and let `P` be a
projection commuting with `rho(C)`.  Define the two raw branch operators

```text
X_w=rho(h_w)P,
Y_w=rho(w)rho(h)P rho(w)^*.                             (RWR3)
```

Then

```text
X_w=Y_w,
X_w^*X_w=P,
X_wX_w^*=A_w:=rho(h_w)P rho(h_w)^*.                     (RWR4)
```

Consequently the two competing `s_12`--`s_23` rectangle transports

```text
L=X_(w_2)X_(w_1)^*,       M=Y_(w_2)Y_(w_1)^*           (RWR5)
```

are equal, and their relative return on `A_(w_1)` is exactly the corner
identity:

```text
L^*M=A_(w_1).                                           (RWR6)
```

No multiplicity unitary can absorb or change this raw loop: equality occurs
between the ambient group words before compression.

The same statement is dimension-free for approximate assignments.  Put

```text
eta_w=||rho(h_w)-rho(w)rho(h)rho(w)^*||_2,
kappa_w=||[P,rho(w)]||_2.                               (RWR7)
```

Then

```text
||X_w-Y_w||_2<=eta_w+kappa_w,
||L-M||_2<=sum_(w=w_1,w_2)(eta_w+kappa_w).              (RWR8)
```

All constants are one and independent of matrix dimension.

## Exact authentication interface

Let `E_w` be a proposed decoded projection and suppose

```text
tau(E_w)=tau(A_w)=tau(P).
```

The raw branch compression has the exact Gram identity

```text
||E_w-A_w||_2^2
 =2(tau(P)-||E_w X_w||_2^2).                            (RWR9)
```

Thus equal rank plus source fullness of `E_wX_w` forces `E_w=A_w`; an
approximate source-Gram deficit gives dimension-free decoded-to-raw
proximity.  Once `(RWR9)` holds for the two endpoints, `(RWR8)` transfers the
pinned raw rectangle to the decoded carriers.

This positive interface does not apply to the current 42-shell decoder.  A
shell atom has trace `1/42`, whereas the native balanced lamp projection has
trace `1/2` and each positive joint atom of two independent balanced lamps
has trace `1/4`.  Before any angle estimate,

```text
tau(P)-||E_wX_w||_2^2 >= tau(P)-tau(E_w),                (RWR10)
```

which is a fixed positive floor for either raw choice.  This is the local
source-fullness form of the aggregate obstruction in
`balanced-raw-lamp-orbit-cannot-approximate-shell-pvm`.

Therefore the actual denominator section identities do remove the abstract
triangle's multiplicity holonomy on literal raw corners.  They do **not**
transfer that pinning to the decoded 42-atom carrier without a rank-matched
joint-atom construction or a different, non-pointwise authentication map.
An external multiplicity PVM can still carry the free loop from
`three-chart-loop-retains-free-multiplicity-holonomy` because `(RWR10)`
prevents it from satisfying the raw source-fullness premise.

The natural finite rank refinement is also fenced.
`sl3-one-over-forty-two-packet-is-external-or-folded` proves that no internal
finite-subgroup character idempotent has trace `1/42`, while any exact finite
packet atom fixed by `C` is fixed by `A` through co-density.  A 21-atom
refinement therefore either stays under one invariant support and cannot
host the 42 orthogonal branches, or moves under `C` and loses the raw section
identity used above.
