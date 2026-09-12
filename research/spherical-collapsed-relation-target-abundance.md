---
rg: 2
id: spherical-collapsed-relation-target-abundance
kind: claim
title: Every good spherical relation edge has a large reservoir of literally shared next targets
artifacts:
  - research/spherical-relation-quadruple-counts.md
---

Let `gh=k` be one tested multiplication relation and let the radius-one
candidate graphs be

```text
A_w(i,j)=1[||U_w x_i-x_j||<=1].
```

Put

```text
eta_i=||(U_g U_h-U_k)x_i||.
```

If `eta_i<=1/16`, then **every** `h`-candidate `j` for `i` has the following
literal relation reservoir: the two radius-one caps centered at

```text
a=U_k x_i,   b=U_g x_j
```

contain a common spherical ball of Euclidean radius `1/4`.

Consequently, if `q_d` is the uniform measure of a radius-`1/4` spherical
ball and `N=N(d)` is chosen with `N q_d >> log N`, then for an iid uniform
sphere cloud, with probability tending to one simultaneously over every
finite tested relation and every pair `(i,j)` with `eta_i<=1/16` and
`A_h(i,j)=1`, there are at least

```text
(1-o(1)) N q_d
```

indices `l` satisfying the **collapsed** constraints

```text
A_g(j,l)=1,   A_k(i,l)=1.
```

If the normalized-HS multiplication defects tend to zero, all but `o(N)`
roots satisfy `eta_i<=1/16`.  Hence the equality slot `l=m` required by the
Schreier relation is not a rare `1/N` coincidence inside the four-slot
relation hypergraph: every good first-step edge has an exponentially small
but macroscopically populated common-target reservoir once the cloud size is
allowed to be sufficiently large.
