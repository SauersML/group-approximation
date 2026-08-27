---
rg: 2
id: two-bit-tag-routing-splits-s3-exit-and-survivor
kind: claim
title: Two site-tag bits route the S3 exit atom and its three-atom survivor complement
distinct_from:
  thompson-site-pulses-localize-hard-exits: that uses one binary pulse after the source exit has already been isolated; this encodes the entire four-atom endpoint table so the exit and survivor images are complementary by construction.
  s3-affine-hnn-transports-the-active-vector: that transports the endpoint table to another occurrence without a first-hit prefix; this transports it into a fresh two-bit tag table whose distinguished atom defines that prefix.
  packet-central-active-complement-reduces-shared-words: that proves the analytic three-atom union reduces the shared algebra; this proves the orthogonal first-hit and survivor placement of that union.
---

At site `n`, let `T_(n,1),T_(n,2)` be commuting self-adjoint involutions,
with all tag bits at distinct sites commuting.  Define

```text
E_n=(I-T_(n,1))(I-T_(n,2))/4,
S_n=I-E_n,
C_0=I,
C_n=product_(k<n) S_k,
X_n=C_n E_n.                                           (TBT1)
```

Then

```text
C_(n+1)=C_n-X_n,        X_j X_n=0 (j<n),
sum_(n<N) tau(X_n)<=1.                                 (TBT2)
```

Let `J,K,b` be an exact elementary-abelian S3 endpoint chart on a reducing
carrier `R_n<=C_n`, and write

```text
P_exit=R_n(I-K)(I-b)/4,
P_live=R_n-P_exit.                                     (TBT3)
```

If a unitary `u_n` preserves every earlier tag bit and implements an
invertible affine identification of the marked endpoint character square
with the tag square, chosen so that `K=b=-1` maps to `T_(n,1)=T_(n,2)=-1`,
then

```text
u_n P_exit u_n^* <= X_n,
u_n P_live u_n^* <= C_(n+1).                           (TBT4)
```

Thus one fresh tag table simultaneously charges exactly the joint exit and
places all three remaining affine atoms under the next survivor prefix.  No
scalar group word represents `P_live`; it is the analytic complement of one
tag atom.

There is a fixed-depth normalized-HS version.  Exactify the finite endpoint
and tag tables first.  If `e_1,e_2` are the two endpoint-to-tag covariance
defects, `p_n` is the sum of commutator defects with earlier tag bits, and
`ell_n=||(I-C_n)R_n||_2`, fixed polynomial telescoping gives

```text
||(I-X_n)u_nP_exit||_2
 +||(I-C_(n+1))u_nP_live||_2
 <= 2 ell_n + p_n + e_1+e_2.                           (TBT5)
```

The constant is independent of ambient matrix dimension.  For any fixed
recurrence depth, the Thompson point-stabilizer presentation of the bridge
orbit makes `p_n` polynomial in the level and in the named relator defect.
