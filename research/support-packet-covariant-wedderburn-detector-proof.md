---
rg: 2
id: support-packet-covariant-wedderburn-detector-proof
kind: route
title: Compute the packet fusion signatures and maximize the factor-overlap transportation form
target: support-packet-covariant-wedderburn-detector
requires:
  - support-failure-packet-has-explicit-hs-payment
---

The four identities in `(CWD1)` directly verify `(CWD2)`.  For example,

```text
[p_1,q_1q_2]=J(Jz_e)=z_e=alpha(J),
[p_2,q_1q_2]=z_f=alpha(z_f),
```

and the other two are fixed.  The shear and the central swap are both
involutions.  Pullback acts on central characters by swapping their first two
bits, hence carries `011` to `101` and proves the assertion after `(CWD3)`.

The packet character table is particularly small.  At central character
`k=(j,e,f)`, its commutation matrix is

```text
[[j,j+e],[f,0]].                                      (1)
```

Row/column reduction gives 38 irreducibles in total: sixteen one-dimensional
simples over `000`, four two-dimensional simples over each rank-one central
character, and one four-dimensional simple over each of `011,101`.  For
characters `chi,psi`, tensor multiplicities are computed by

```text
<chi psi,theta>=(1/128) sum_(g in B_sub)
                 chi(g) psi(g) conjugate(theta(g)).   (2)
```

Applying `(2)` to `(CWD3)` gives `(CWD5)` for every radical label.  On `101`
it gives respectively

```text
(2,2)^4,(3,4),          (1,1)^16,(3,4),               (3)
```

which amplifies to `(CWD6)`.  The standard-library verifier constructs all 38
Pauli-normal-form irreducibles, checks their orthogonality and
`sum dim(T)^2=128`, and reproduces `(2)` exhaustively.

It remains to prove the uniform distance.  Ignore the common `M_(3m)` factor
for the moment.  On each of the four remaining `4m`-dimensional plus blocks,
the algebra is

```text
I_2 tensor M_(2m),
```

while the minus algebra has sixteen `M_m` factors in total.  For a factor
`I_d tensor M_r` supported on a projection `P` and a factor
`I_e tensor M_s` supported on `Q`, Schur orthogonality followed by
Cauchy--Schwarz gives the Reynolds-overlap bound

```text
Tr_super(E_(d,r) E_(e,s)) <= Tr(PQ)^2/(de).           (4)
```

Put `x_ij=Tr(P_iQ_j)/m`.  The `x_ij` form a transportation matrix: the five
plus row margins are `4,4,4,4,12`, the seventeen minus column margins are
`1` repeated sixteen times and `12`, and all entries are nonnegative.  By
`(4)`, the total Reynolds overlap is at most

```text
sum_(i,j) x_ij^2/(d_i e_j) m^2,                      (5)
```

where `d_i=(2,2,2,2,4)` and `e_j=(1^16,4)`.  The
transportation polytope has integral vertices.  At a vertex each unit column
is assigned to one row.  If `y_i` is the amount of the final size-12 column
assigned to row `i`, maximizing `(5)` reduces to

```text
sum_(i<=4) [y_i^2/8+(4-y_i)/2]
 + y_5^2/16+(12-y_5)/4,
0<=y_i<=4, 0<=y_5<=12, sum_i y_i=12.                 (6)
```

The convex expression `(6)` is at most `17`, with equality at
`y_1=...=y_4=0,y_5=12`.  Therefore

```text
Tr_super(R_+ Ad_W R_- Ad_W^*) <=17m^2.                (7)
```

Both Reynolds projections have rank `25m^2`, so `(7)` gives unnormalized
squared distance at least

```text
50m^2-2(17m^2)=16m^2.
```

Division by `(28m)^2` proves `(CWD7)`.  The separate numerical optimizer
starts at the equality alignment in `(6)` and attempts to falsify it over
`U(28)`; it returns overlap `17` and distance `1/49`, but no numerical fact is
used in the proof.
