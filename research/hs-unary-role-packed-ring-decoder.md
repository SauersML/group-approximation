---
rg: 2
id: hs-unary-role-packed-ring-decoder
kind: claim
title: Decode the unary role-packed conditional ring ladder on one physical HS carrier
distinct_from:
  hs-finite-adaptive-ring-tree-decoder: that must synchronize an M-ary family of representation-dependent outgoing sources; this has one fixed aggregate source and one successor at every level.
  bcs-atom-detects-its-e5-central-root: that asks only for local support of one selected atom on one root; this also carries the decoded physical carrier through the finite unary sequence.
  role-packed-bcs-gap-is-one-idempotent: that proves the exact aggregate idempotent and its robust BCS mass; this is the remaining group-microstate interpretation of its conditional arrows.
---

**OPEN UNARY METRIC DECODER.**  Use the fixed aggregate forbidden
idempotent `B_f` from `role-packed-bcs-gap-is-one-idempotent`.  Choose a
depth `N` and form the finite coefficient ladder

```text
a_n=q_n B_f,
sbar_n s_n=a_n,
s_n sbar_n=d_n,
d_n q_n=q_n d_n=0,
q_(n+1)=q_n+d_n,                    0<=n<N,             (URD1)
```

with every `q_n` required to commute with the shared BCS tuple and the full
role packet.  Apply rank-five Steinberg wordization.

Prove that there are `c>0`, `C<infinity`, independent of matrix dimension,
such that every sufficiently accurate canonical normalized-HS microstate
with the central mark separated supplies physical projections

```text
Q_0,...,Q_N<=Q_- ,       D_0,...,D_(N-1)<=Q_-          (URD2)
```

on one matrix space satisfying, up to `C sqrt(E)` total error,

```text
Q_0=the corrected Pauli quarter carrier,
[Q_n,BCS and role packet]=0,
D_n Q_n=0,
Q_(n+1)>=Q_n+D_n,
tau(D_n)>=c tau(Q_n B_f).                              (URD3)
```

It is enough for `(URD3)` to hold only along this one fixed finite chain.
The aggregate gap then gives

```text
tau(Q_(n+1))
 >=(1+c beta/m)tau(Q_n)-C' sqrt(E).                    (URD4)
```

Taking `(1+c beta/m)^N>2` contradicts
`tau(Q_0)->1/4` and `Q_N<=Q_-`, `tau(Q_-)->1/2`.

This is strictly smaller than the M-ary decoder.  There is one source at
each level, so no representation-dependent maximum, arbitrary-list SELECT,
or compatibility among several outgoing orientations remains.  The exact
three-line first-hit table and its Murray--von Neumann swap solve the local
source/range equality and orthogonal-sum equation.  The two-pair E5 cell
uniformizes the spectator coordinates after the aggregate source root has
been detected.

The unresolved content inside this particular coefficient-root
implementation has two sequential parts:

1. transfer a fixed fraction of the actual payload projection `Q_nB_f` to
   the nontrivial central-root support of `x_13(a_n)` and hence to the
   spectator-trivial source fiber;
2. make the oriented sum produced at level `n` the same physical reducing
   carrier used as `Q_(n+1)` at the next level.

The second clause is not a fundamental carrier theorem.  The direct route
`finite-depth-role-packed-aggregate-escape` discards the prescribed
coefficient projection after each step and takes the analytic reducing hull
of the transported aggregate source.  By
`reducing-hull-carry-forward-after-aggregate-escape`, that hull is
automatically a valid next carrier and has the required trace gain.  Thus
one may bypass this full ring decoder entirely.  On that strictly smaller
route the only open statement is a fixed positive overlap loss for `Q_nB_f`
along the finitely many reached carriers.

Separate finite root-window PVMs do not prove either clause.  They may place
the source and sum tables on incompatible multiplicity reservoirs, while a
tensor-independent role/address refinement is trace-neutral by
`independent-address-capacity-cannot-drive-selected-atom-growth`.  What has
been removed is only the cross-branch orientation obstruction; the remaining
payload-to-root and successive-carrier coupling is still genuinely
matrix-only.

Nor does the coefficient eigenvalue covariance solve the first clause.
Relations of the form `u_j a=plus_or_minus a` make the corresponding BCS
involutions conjugate the root `x_13(a)` to itself or its inverse, but
`root-scaling-covariance-does-not-detect-bcs-atom` has an exact marked
one-dimensional model with the desired BCS character and the root equal to
one.  The missing row must therefore exclude the root-kernel quotient on the
actual aggregate payload carrier; finite root automorphisms alone cannot do
it.

The perfect tracial model remains consistent: `B_f=0`, so set every arrow
and `d_n` to zero and keep all `q_n=q_0`.  Thus the desired decoder is not a
universal tracial identity.
