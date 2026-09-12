---
rg: 2
id: stw87-index-two-amalgam-parity-proof
kind: route
title: Apply two-sheet orbit sums to the dihedral-type virtually cyclic amalgam
target: stw87-virtually-cyclic-actions-have-dimension-one
requires:
  - stw87-zero-dimensional-minimal-actions-have-dimension-one
---

## The virtually cyclic dichotomy

The algebraic classification of infinite virtually cyclic groups gives two
types.  In type I there is an exact sequence

```text
1 -> F -> G -> Z -> 1                                  (VCP1)
```

with `F` finite.  In type II, `(VC2)` holds.  One quick description uses
the action on the two ends: the orientation-preserving subgroup is
finite-by-cyclic; if no end-reverser exists one obtains `(VCP1)`, while in
the other case quotienting by the maximal finite normal subgroup gives
`D_infinity`.  The inverse images of its two reflection subgroups are the
finite vertex groups in `(VC2)`, with common index-two subgroup `F`.

For type I, the existing PV argument in
`stw87-zero-dimensional-minimal-actions-have-dimension-one` applies to the
epimorphism onto `Z` and excludes nuclear dimension zero.

## K-theory of the index-two amalgam

Now assume `(VC2)` and let `G` act pointwise freely on a nonempty compact
zero-dimensional Hausdorff space `K`.  Put

```text
C=C(K),        D=C crossed_product F,
B_i=C crossed_product G_i.                              (VCP2)
```

A free action of a finite group on a compact zero-dimensional space has a
clopen fundamental domain: refine finitely many clopen displacement covers
and choose one atom in each finite orbit.  Hence the finite crossed products
in `(VCP2)` are matrix algebras over their orbit spaces.  In particular,

```text
K_0(D)=C(K/F,Z),             K_1(D)=0,
K_0(B_i)=C(K/G_i,Z),         K_1(B_i)=0.                (VCP3)
```

These identities remain valid without metrizability, by continuity over
finite clopen partitions.  Under `(VCP3)`, the inclusion `D -> B_i` induces
the index-two orbit-sum map

```text
S_i:C(K/F,Z) -> C(K/G_i,Z),
S_i(f)(G_i x)=f(Fx)+f(Fg_i x),                          (VCP4)
```

where `g_i` represents the nontrivial coset in `G_i/F`.  Pointwise freeness
makes the two `F`-orbits in `(VCP4)` distinct.

Pimsner's `KK`-theoretic exact sequence for crossed products by groups acting
on trees (Invent. Math. 86 (1986), 603--634,
doi:10.1007/BF01389271) applies to this one-edge graph of groups.  For separable
`G`-invariant coefficient algebras it gives the displayed map below.  For
arbitrary `K`, write `C(K)` as the directed union of its separable
`G`-invariant unital subalgebras; reduced crossed products by the amenable
group `G` and `K`-theory commute with this directed limit.  Thus the same
sequence holds without metrizability.  Since all three odd groups in
`(VCP3)` vanish, it reduces to

```text
K_0(C crossed_product_r G)=coker(Phi),
K_1(C crossed_product_r G)=ker(Phi),

Phi:C(K/F,Z) -> C(K/G_1,Z) direct_sum C(K/G_2,Z),
Phi(f)=(S_1(f),-S_2(f)).                               (VCP5)
```

## The parity dichotomy

Let `eta=(1,-1)` in the codomain of `Phi`.  Both coverings in `(VCP4)` have
two sheets, so

```text
Phi(1)=(2,-2)=2 eta.                                   (VCP6)
```

If `[eta]` is nonzero in `coker(Phi)`, equations `(VCP5)--(VCP6)` give a
nonzero element of order two in `K_0(C crossed_product_r G)`.

If `[eta]=0`, choose `f in C(K/F,Z)` with

```text
S_1(f)=S_2(f)=1.
```

Then `h=2f-1` is pointwise odd and hence nonzero, while

```text
S_1(h)=S_2(h)=0.
```

Thus `0!=h in ker(Phi)=K_1(C crossed_product_r G)`.  In either case the
crossed product is not locally AF: locally AF algebras have torsion-free
`K_0` and zero `K_1`, also in the nonseparable case because every finite
K-theory witness lies in a separable AF subalgebra.

For a minimal action, the existing virtually nilpotent theorem gives nuclear
dimension at most one.  Nuclear dimension zero is local AF, which the type I
PV index or the type II parity dichotomy excludes.  This proves `(VC1)`.
