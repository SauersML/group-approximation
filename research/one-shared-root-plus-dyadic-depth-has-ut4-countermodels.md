---
rg: 2
id: one-shared-root-plus-dyadic-depth-has-ut4-countermodels
kind: claim
title: One literal shared Heisenberg root plus dyadic depth transport has canonical UT4 countermodels
distinct_from:
  one-shared-root-does-not-align-heisenberg-packets: that identifies a central root in one regular Heisenberg packet with a simple root in another by an arbitrary spectral conjugacy; this makes the shared root literal algebraically inside one unitriangular group and imposes one common exact dyadic automorphism on both packets.
  heisenberg-chamber-clocks-escape-until-root-gluing: that duplicates geometrically repeated roots between separate chamber factors; this uses one globally named shared root on one coefficient reservoir, but only for an open two-triangle chain rather than the closed A2 Weyl gallery.
  periodic-conductor-plateaux-pay-a-shared-root-seam: that proves separated block plateaux pay when the literal A2 wall occurrences are identified; this gives a non-separated finite common-reservoir calibration showing that a single shared occurrence and its depth transport are still insufficient without the Weyl return.
---

Put `R=Z[1/2]` and `N=UT_4(R)`, with elementary roots `x_ij(t)`.  The two
literal Heisenberg packets

```text
<x_12,x_23,x_13>,       [x_12(s),x_23(t)]=x_13(st),
<x_13,x_34,x_14>,       [x_13(s),x_34(t)]=x_14(st)       (USD1)
```

share the **same** root subgroup `x_13(R)`: it is central in the first
packet and a simple input of the second.  Define the dyadic automorphism

```text
alpha(x_ij(t))=x_ij(2^(j-i)t).                           (USD2)
```

The height additivity `(k-i)=(j-i)+(k-j)` makes `(USD2)` preserve every
Steinberg multiplication relation, including both equations in `(USD1)`.
Let

```text
L=N rtimes_alpha <h>,
G=(direct_sum_(k in Z) C_2) rtimes L,                    (USD3)
```

where `N` fixes the base lamp and `h` translates the lamp coordinate.
Then all of the following hold exactly in one group:

1. two noncommuting Heisenberg packets on one coefficient reservoir;
2. one literal root occurrence shared between them;
3. one common invertible dyadic depth transport on every root; and
4. a balanced base lamp commuting with the whole coefficient group whose
   `h`-translate is a distinct commuting lamp.

Moreover `G` has canonical finite matrix models preserving the forbidden
overlap.  For `L_0>=2`, put `q=2^L_0-1`, reduce `R` modulo `q`, and reduce
the depth coordinate modulo `L_0`.  Since `2^L_0=1 mod q`, `alpha^L_0=1`
on `UT_4(Z/qZ)`, giving the finite quotient

```text
G_L=(direct_sum_(Z/L_0) C_2)
      rtimes (UT_4(Z/qZ) rtimes_alpha Z/L_0).            (USD4)
```

These quotients separate every fixed nonidentity word for all sufficiently
large suitable `L_0`.  Their left regular representations therefore have
canonical limiting character.  With

```text
P=(1-c_0)/2,             Q=hPh^(-1),
```

they satisfy identically

```text
tr(P)=tr(Q)=1/2,       [P,Q]=0,       tr(PQ)=1/4.        (USD5)
```

Thus the first proposed unfenced packet—one globally shared arithmetic root
across two local Heisenberg charts plus exact dyadic depth transport—still
admits finite canonical countermodels.  What `(USD1)--(USD5)` omit is the
closed `A_2` Weyl gallery: opposite/simple root identifications return the
open chain to the same three-dimensional Chevalley reservoir.  That return,
not one shared root or one rank-two commutator, is the smallest remaining
native relation type capable of detecting the lamp multiplicity.

