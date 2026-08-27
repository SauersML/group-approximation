---
rg: 2
id: odd-congruence-native-sector-has-defect-only-gap
kind: claim
title: The odd-congruence native lamp sector has a uniform defect-only four-atom gap
distinct_from:
  odd-congruence-lambda-exact-sector-collapses: that proves qualitative relative-commutant collapse in matrix ultraproducts for every exact congruence restriction away from the denominator prime; this extracts the uniform finite-dimensional linear inequality for the balanced commuting-conjugate lamp packet.
  native-transfer-has-defect-only-certificate: that reduces the full native problem to a universal defect-only inequality over arbitrary assignments; this proves that inequality only on the exact odd-congruence lattice face, with no actor trace hypothesis.
  exact-projective-codensity-has-a-uniform-trace-square-gap: that assumes an exact representation of the entire ambient arithmetic group and treats every auxiliary unitary; this allows the ambient presentation relations to have small defect but assumes the lattice restriction is an exact odd-congruence representation, and treats only the native involution packet.
---

ESTABLISHED.  Put

```text
Lambda=SL_3(Z) < Gamma=SL_3(Z[1/2]),
h=diag(2,1,1/2),
```

and fix a finite presentation of `Gamma` and words for a finite generating
set of `Lambda`.  There is `L_odd<infinity` with the following property in
every matrix dimension.

Let `rho` be an assignment of the ambient presentation generators whose
restriction to `Lambda` is a genuine finite-dimensional representation
factoring through `SL_3(Z/m)` for some odd `m`.  Let `c` be an exact
trace-zero self-adjoint involution.  With `d_cc` and `e_h` as in
`native-transfer-has-defect-only-certificate`, one has

```text
e_h(rho,c) <= L_odd d_cc(rho,c).                         (ONG1)
```

There is no canonical-character condition and no restriction on the
irreducible multiplicities of the exact lattice representation.  In the
exact commuting case, for

```text
P=(I-c)/2,       Q=rho(h)P rho(h)^*,       a=tr(PQ),
```

this becomes

```text
8a(1-2a) <= L_odd d_cc(rho,c).                           (ONG2)
```

Thus a failure of the full defect-only native inequality cannot live on the
odd-congruence exact face.  It must use either an exact congruence profile
with a nontrivial two-primary component (including the scale-spread weight
escape), or a lattice assignment at uniform positive distance from every
genuine representation.

## Determinant and parity audit

No determinant refinement strengthens `(ONG2)`.  When `P,Q` commute and
both have rank `d/2`, write `c=I-2P`, `d_h=I-2Q`.  Their joint atoms have
ranks

```text
r_11=r_00=ad,       r_10=r_01=d/2-ad.                   (ONG3)
```

The target word `c d_h` is `-1` precisely on the two cross atoms, so its
negative multiplicity is

```text
r_10+r_01=d-2ad=2(d/2-ad),                              (ONG4)
```

which is automatically even.  Hence

```text
det(c d_h)=1                                            (ONG5)
```

for every allowed overlap, including `a=0`, `1/4`, and `1/2`.  Also
`det(c)=det(d_h)=(-1)^(d/2)`.  Every word in the commuting pair reduces to
`c^epsilon d_h^eta`, so all determinant characters of the native two-lamp
packet are independent of the interior-versus-endpoint distinction.  Atom
rank parity can be changed by a common spectator doubling while normalized
HS defects and `a` remain fixed.  The positive gap above therefore comes
from the rank-two arithmetic collapse, not from determinant or parity.
