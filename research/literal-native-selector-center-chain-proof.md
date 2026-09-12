---
rg: 2
id: literal-native-selector-center-chain-proof
kind: route
title: Read the forced composable q-centers from the Steinberg incidence equations
target: literal-selector-roots-force-center-chain
requires: []
---

The own-cell identity in `(LNS1)` uses the Steinberg relation

```text
[x_ij(r),x_jk(s)]=x_ik(rs).
```

To obtain the ordered product `b_(m+1)a_m` from
`[B_(m+1),A_m]` by this same relation, the terminal index of
`B_(m+1)` must be the initial index of `A_m`.  In the notation of `(LNS1)`
this is precisely `(LNS2)`.

Substitution into the own centers gives

```text
C_(m+1)=x_(alpha_(m+1),alpha_m)(q),
C_m=x_(alpha_m,delta_m)(q).
```

They are again a composable Steinberg pair, so their commutator is the root
described after `(LNS3)` when their two outer indices are distinct.  The
coefficient `q=s_1t_1` is a nonzero idempotent:

```text
q^2=s_1(t_1s_1)t_1=s_1t_1=q.
```

The image of `x_(alpha_(m+1),delta_m)(q)` in the elementary matrix group is
`I+qE_(alpha_(m+1),delta_m)`, which is not the identity.  Hence the root is
nonidentity already in the Steinberg group, proving that the consecutive
centers do not commute in that case.

If `alpha_(m+1)=delta_m`, write this common index as `k` and
`alpha_m=j`.  The elementary images of the two centers are
`I+qE_(k,j)` and `I+qE_(j,k)`.  Their products in the two orders differ by
the diagonal term: one contains `q^2E_(k,k)=qE_(k,k)`, while the other
contains `q^2E_(j,j)=qE_(j,j)`.  They therefore do not commute in the
elementary group, and hence cannot commute in the Steinberg group either.

For `(LNS4)`, prefix cancellation gives

```text
b_2a_1=s_(00)t_1s_1t_0=s_(00)t_0,
b_3a_2=s_(000)t_1s_1t_(00)=s_(000)t_(00).
```

Applying the same Steinberg relation proves `(LNS5)`, while its application
to the centers gives the two displayed nontrivial commutators.  Finally
`q a_m=a_m`, again by `t_1s_1=1`, so applying the relation to `(C_2,A_1)`
and `(C_3,A_2)` gives `(LNS6)`.  Thus the later center fails to commute with
the earlier arm, proving the asserted failure of the simultaneous reducing
Pauli packet and completing the proof.
