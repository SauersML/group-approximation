---
rg: 2
id: literal-sync4-c2-amalgam-has-zero-selected-meet
kind: claim
title: Literal SYNC4 reflection amalgamation makes the two one-negative carriers disjoint
distinct_from:
  finite-product-selected-type-mark-does-not-align-carriers: that gives the scalar C2*C2 warning that a nonzero product need not contain a common meet; this computes the actual one-negative SYNC4 packet after the desired coordinate reflections have already been identified literally.
  role-hyperoctahedral-type-has-an-orthogonal-amalgam-model: that uses the balanced irreducible role packet and a D8 amalgam; this uses the rank-free abelian one-negative corner and the minimal C2 edge dictated by one SYNC4 incidence.
  finite-graph-packet-compression-wandering-no-go: that rules out a compressed wandering return in every finite Bass--Serre packet; this proves that even the non-wandering literal coordinate identification has zero selected intersection.
---

**ESTABLISHED.**  Let

```text
K_L=(C_2)^4=<r_(L,0),...,r_(L,3)>,
K_R=(C_2)^4=<r_(R,0),...,r_(R,3)>
```

and form the minimal ordinary-group implementation of one `SYNC_4`
incidence by identifying the two required coordinate reflections,

```text
G=K_L *_(<s>) K_R,
s=r_(L,j)=r_(R,0).                                    (LSA1)
```

Let `q_L,q_R` be the one-negative character projections from
`sync4-one-negative-abelian-corner-wordizes-arbitrary-pvm`.  Then in the
canonical group von Neumann algebra

```text
q_L meet q_R=0.                                        (LSA2)
```

Thus literal amalgamation of the two atom-reflection group elements does
make their ambient words equal, but leaves no nonzero carrier on which both
local four-outcome decoders are valid.  This refutes the smallest apparent
solution of `sync4-coordinate-atom-groupifier-cell`.

The obstruction is already quantitative.  With

```text
e_-=(1-s)/2,             e_+=(1+s)/2,
```

the two free selected projections in the normalized central corners have
traces

```text
tau_(e_-)(q_L e_-)=tau_(e_-)(q_R e_-)=1/8,
tau_(e_+)(q_L e_+)=tau_(e_+)(q_R e_+)=3/8.             (LSA3)
```

Consequently the standard free-projection calculation gives

```text
||q_L q_R e_-||=sqrt(7)/4,
||q_L q_R e_+||=sqrt(15)/4,                             (LSA4)
```

both strictly below one.  A vector in the common range would be fixed by
the corresponding product, proving `(LSA2)`.

The group in `(LSA1)` is a finite amalgam of finite groups, hence virtually
free and residually finite.  Its canonical trace is therefore visible in
finite exact models; the zero-meet phenomenon is not an artifact of an
unavailable infinite representation.

The surviving `SYNC_4` route must consequently add a non-Bass--Serre
same-block return or a finite-support group-ring coupling that changes the
relative one-negative carrier geometry.  Identifying the coordinate words
alone cannot do so.

