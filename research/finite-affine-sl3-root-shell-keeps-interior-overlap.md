---
rg: 2
id: finite-affine-sl3-root-shell-keeps-interior-overlap
kind: claim
title: A finite affine SL3 root shell satisfies the Weyl triangle while keeping independent lamp overlap
distinct_from:
  affine-weyl-apartment-has-independent-lamp-models: that uses only the torus normalizer of one apartment; this includes the full nonmonomial root group SL3(F2), its action on every direction in the finite shell, and the rank-two Weyl triangle.
  rank-two-weyl-triangle-is-first-apartment-gauge-detector: that proves the triangle kills a corrector already lying in the full coefficient commutant; this gives an exact model in which the directional gauges are transported by the root group but never align into such a common commutant gauge.
  commuting-conjugate-involution-transfer-for-sl3-pair: that includes the genuine dyadic root-scaling relations of SL3(Z[1/2]); this identifies one such scaling relation as the first exact arithmetic input absent from the finite countermodel.
---

Let

```text
M = F_2^3,                 K = SL_3(F_2),
L = M rtimes K,
```

where `L` acts affinely on `M`.  Put

```text
B = (direct_sum_(x in M) C_2) rtimes L,                 (FAS1)
```

and write `c_x` for the coordinate lamps.  This is a finite group.  The
linear subgroup `K` fixes `0`, so

```text
[c_0,K]=1.                                                (FAS2)
```

In particular `(FAS2)` holds for every elementary transvection in the full
nonmonomial root packet `SL_3(F_2)`, not only for signed permutation/Weyl
elements.

Choose

```text
v = (1,0,1) in M,             h = (v,1) in L.
```

Let `s_12,s_23 in K` be the two coordinate transpositions (over `F_2` their
determinant is one), and set

```text
h'  = s_12 h s_12^-1,
h'' = s_23 h s_23^-1.
```

Their translation vectors are

```text
v'  = (0,1,1),
v'' = (1,1,0).
```

Since subtraction equals addition in `F_2^3`,

```text
v-v''=v+v''=v',
```

and therefore the exact rank-two diagonal relation holds:

```text
h (h'')^-1 = h'.                                        (FAS3)
```

Moreover every `k in K` transports the first translated lamp by

```text
k (h c_0 h^-1) k^-1 = c_(kv).                           (FAS4)
```

Thus the complete finite root group coherently glues the apartment direction
`v` to all directions in its nonmonomial orbit.  All those lamps commute in
`B`, a condition stronger than the native Hecke-edge commutations.

## Exact interior overlap

Let `lambda` be the left regular representation of the finite group `B` and
put

```text
P=(1-lambda(c_0))/2,
Q=lambda(h)P lambda(h)^*=(1-lambda(c_v))/2.
```

The four group elements `1,c_0,c_v,c_0c_v` are distinct.  Hence

```text
tr(P)=tr(Q)=1/2,
[P,Q]=0,
tr(PQ)=1/4,
tr(lambda(c_0 h c_0 h^-1))=0.                           (FAS5)
```

All relations `(FAS2)--(FAS4)`, all internal Steinberg/root relations of
`SL_3(F_2)`, every root transport `(FAS4)`, and the full finite-group
canonical trace hold exactly in one finite matrix algebra.  Consequently
the following inputs do **not** imply common-gauge extraction:

1. a balanced projection fixed by a full rank-two nonmonomial root group;
2. commuting translated projections along the complete root orbit;
3. exact Weyl covariance of those translates; and
4. the rank-two triangle `h(h'')^-1=h'`.

## The first arithmetic relation which the model fails

The model does not represent the dyadic dilation of the actual arithmetic
group.  For the elementary root `u=e_12(1)`, conjugation in `L` gives

```text
(v,1)(0,u)(v,1)^-1 = (v+uv,u),                          (FAS6)
```

whose linear part is still the nontrivial transvection `u`.  In
`SL_3(Z[1/2])`, by contrast,

```text
h e_12(1) h^-1 = e_12(2),                               (FAS7)
```

and reduction modulo two kills the right side.  Thus `(FAS7)` cannot hold in
the affine-shell model.

This locates the smallest missing *type* of input.  Root incidence, Weyl
conjugacy, the three coweight directions, and their triangle still permit the
maximally interior overlap.  A valid common-gauge theorem must use the
noninvertible depth shift `(FAS7)` (and its adjacent-root conjugates) to tie
the directional four-atom decompositions to one root spectral reservoir.
Equivalently, the live matrix-coordinate gate is not merely
cross-apartment consistency; it is

```text
cross-apartment consistency + dyadic root-depth transport.       (FAS8)
```

The countermodel proves that deleting the second term of `(FAS8)` makes the
desired normalized-HS conclusion false even in exact finite matrices.
