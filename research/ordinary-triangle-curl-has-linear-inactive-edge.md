---
rg: 2
id: ordinary-triangle-curl-has-linear-inactive-edge
kind: claim
title: Ordinary triangle curl is linear across inactive code coordinates
distinct_from:
  low-odd-square-removes-pairwise-green-stationarity: that proves edgewise coercivity on the low odd-square sector and leaves a curl estimate; this rules out the untwisted complete-graph triangle curl as that estimate.
  tangent-commutator-covariance-bypasses-code-riesz-endpoint: that uses the endpoint grading available at an exact character pair; this shows why forgetting that grading creates first-order curl.
  quadratic-overlay-has-uniform-linearized-synchronization-gap: that uses the code-character support and its distance; this tests a base-free ordinary Hodge decomposition before the support has been identified.
---

ESTABLISHED NO-GO.  For reflections `(Q_i)`, put

```text
 C_ij=(Q_iQ_j)^2,
 omega_ij=(C_ji-C_ij)/4=-omega_ji.                      (OTC1)
```

The ordinary complete-graph triangle curl

```text
 curl_(i,j,k)=omega_ij+omega_jk+omega_ki               (OTC2)
```

is not quadratic in the pair defects, even arbitrarily close to an exact
commuting code tuple.  More precisely, let `T` be a proper nonempty subset
of `[L]`, with `1 in T`, and on `C^2` put

```text
 S_i=Z  (i in T),       S_i=I  (i notin T),
 Q_1(theta)=cos(2theta)Z+sin(2theta)X,
 Q_i(theta)=S_i  (i!=1).                               (OTC3)
```

This is a reflection tuple converging to the commuting tuple `(S_i)`.  For
every `j in T\{1}` and `k notin T`,

```text
 omega_(1,j)=-(sin(4theta)/2)XZ,
 omega_(j,k)=omega_(k,1)=0,
 curl_(1,j,k)=omega_(1,j).                              (OTC4)
```

Meanwhile the pair odd square from `(LOS1)` is

```text
 R_(1,j)=sin^2(2theta)I.                                (OTC5)
```

Thus every nonzero pair lies in a pointwise low sector `R<=sI` with
`s=sin^2(2theta)->0`, but its triangle curl is still first order.  If
`m=|T|`, and

```text
 E_omega=L^(-2)sum_(i,j)||omega_ij||_2^2,
 E_curl=L^(-3)sum_(i,j,k)||curl_(i,j,k)||_2^2,
```

then the displayed ordered edges and triangles give

```text
 E_curl/E_omega >=(L-m)/(2L).                           (OTC6)
```

Consequently no length-independent estimate

```text
 E_curl<=C s E_omega                                   (OTC7)
```

can hold for ordinary triangles whenever both `m/L` and `1-m/L` stay
positive.

The failure is structural rather than an endpoint spike.  On a fixed pair
of code characters, tangent edge signals occupy the support of their
character difference.  A triangle with one coordinate outside that support
has one live edge and hence linear curl.  The exact-base code proof avoids
this by using the support-dependent grading and the code-distance gap.  A
base-free Hodge proof must therefore construct a twisted/masked triangle
complex from the tuple itself, or recover enough of the character support;
the untwisted complete-graph curl cannot close
`off-base-row-gradient-coercivity`.
