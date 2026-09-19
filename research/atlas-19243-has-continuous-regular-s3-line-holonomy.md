---
rg: 2
id: atlas-19243-has-continuous-regular-s3-line-holonomy
kind: claim
title: Collision 19243 leaves a continuous line-sector holonomy even with exact regular S3 margin and balanced involution
distinct_from:
  atlas-19243-s3-relative-normal-form: that gives one S4 solution with regular S3 margin; this identifies the relative collision group, proves it has an infinite-dihedral quotient, and constructs a continuous family with the exact balanced involution spectrum required by the regular A8 lift.
  atlas-a4-packet-alone-fails-opaque-star: that shows packet constraints without collision leave an order mismatch; this shows collision itself leaves a continuous multiplicity mode and identifies the precise S3 irreducible sectors on which it is blind.
  atlas-a4-collision-assisted-opaque-star-compiler: that asks the joint packet/collision system to control all covariance opcodes; this proves the collision part cannot control the trivial/sign multiplicity angle and isolates the cross-component packet transfer still required.
---

Use the relative collision presentation from
`atlas-19243-s3-relative-normal-form`:

```text
P=<r,s,c | r^3=s^2=c^2=1, srs=r^(-1),
               r c s c r^(-1) c (s r)c=1>.             (CRH1)
```

Put `x=cs`, so `c=xs`.  Then `(CRH1)` is equivalently

```text
s x s=x^(-1),
r x^2 r=x r x.                                         (CRH2)
```

In particular `P` maps onto the infinite dihedral group by killing `r` and
leaving `s,c` as its two free involutions.  The collision cell is therefore
not a finite relative representation category.

More sharply, it has a continuous family of finite-dimensional unitary
representations `pi_theta` with exactly the local margins needed in the atlas.
Decompose a six-dimensional space as

```text
(triv direct_sum sign) direct_sum std_+ direct_sum std_-, (CRH3)
```

where `std_+` and `std_-` are two copies of the two-dimensional standard
representation of `S3=<r,s>`.  On the first two-dimensional summand put

```text
r=1,
s=diag(1,-1),
c=c_theta,                                              (CRH4)
```

where `c_theta` is an arbitrary real reflection.  On `std_+` put `c=+1`, and
on `std_-` put `c=-1`.  Every `pi_theta` satisfies the collision relation.
Its restriction to `<r,s>` is

```text
triv direct_sum sign direct_sum 2 std = Reg(S3),        (CRH5)
```

and `c` has three `+1` and three `-1` eigenvalues.  Hence, after taking `3360`
copies, `(CRH3)--(CRH5)` lives on the restriction

```text
Reg(A8)|_S3 =3360 Reg(S3)                               (CRH6)
```

and its collision involution is unitarily conjugate to the regular matrix of
any nonidentity involution of `A8`.

Thus exact collision, exact regular `S3` restriction, and the exact balanced
involution conjugacy class leave a full continuous reflection angle.  The
angle lies entirely in the `triv direct_sum sign` part of the `S3` margin;
collision is identically satisfied there because `r=1`.  No collision-only
spectral or character estimate can control this mode.

For the opaque-star program this identifies the first genuinely joint gate:
the two packet bicliques and their common relative frame must transfer the
standard-sector rigidity into the trivial/sign collision sector.  A proof
which first replaces collision by a finite list of `S3` representation types,
or which treats its balanced involution spectrum as rigid, necessarily misses
the family `(CRH3)--(CRH4)`.

