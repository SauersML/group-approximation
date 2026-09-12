---
rg: 2
id: stw99-lxxvi-higher-nccw-s6-obstruction
kind: claim
title: Higher NCCW cells carry an exact order-two cokernel obstruction
distinct_from:
  stw99-lxxvi-one-dim-nccw-s6-criterion: that computes the complete one-dimensional criterion because the residual pi_6 group vanishes; this gives the recursive obstruction coset in every cell dimension and exposes its order-two and 2-saturation structure.
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Let `B` be unital, let `F` be finite dimensional, let `k>=1`, and form a
unital NCCW cell pullback

```text
A=B pullback_(C(S^(k-1),F)) C(D^k,F)                  (CP)
```

from a unital attaching homomorphism
`theta:B->C(S^(k-1),F)` and boundary restriction.  Write `alpha_A` and
`alpha_B` for the scalar images of

```text
alpha in pi_5(U(2))=Z/2.
```

If `alpha_B` is nonzero, then `alpha_A` is nonzero.  If `alpha_B=0`, there
is a canonical obstruction coset

```text
omega_k(alpha;theta)
 in coker(
   pi_6(U(M_2(B))) -> pi_(5+k)(U(M_2(F)))             (O)
 )
```

such that

```text
alpha_A=0  iff  omega_k(alpha;theta)=0.                (E)
```

The map in `(O)` is the connecting map determined by the attaching
homomorphism.  Concretely, choose a null-homotopy of `alpha_B`, apply
`theta`, and compare it with the constant scalar family on the cell; the
resulting `(5+k)`-sphere in `U(M_2(F))` represents `(O)`.  Changing the
null-homotopy changes the representative exactly by the displayed image.

The cokernel in `(O)` maps injectively to `pi_5(U(M_2(A)))`.  Since
`alpha_A` has order at most two, the canonical coset satisfies

```text
2 omega_k(alpha;theta)=0.                               (T)
```

Thus the scalar class dies whenever the cokernel in `(O)` has no nonzero
element annihilated by two.  Equivalently, it dies whenever the image of the
connecting map is **2-saturated** in `pi_(5+k)(U(M_2(F)))`:

```text
2x in image(boundary_k)  implies  x in image(boundary_k). (2S)
```

This yields an attaching-map-independent positive class.  Suppose a finite
unital NCCW complex starts from

```text
A_0=directSum_i M_(r_i),             r_i>=2,
```

and is built using only cells of odd dimensions `k`.  For every matrix
summand `M_d` in the `k`-cell algebra assume

```text
5+k<4d.                                                   (SR_k)
```

Then the scalar image of `alpha` vanishes in
`pi_5(U(M_2(A)))`, independently of every attaching map.  Indeed `(SR_k)`
puts

```text
pi_(5+k)(U(2d))=pi_(5+k)(U)=0
```

in the stable even degree `5+k`.

More generally, the same conclusion holds for any finite cell tower for
which every connecting-map image is 2-saturated; group vanishing is the
special case with zero target.  In stable even cell dimensions the target is
a free abelian group, not an integer-valued scalar obstruction: survival can
occur only when the connecting image is not 2-saturated and thereby creates
order-two torsion in its cokernel.  In particular, if
`pi_6(U(M_2(B)))=0`, one stable even cell also preserves vanishing for every
attaching map, because its obstruction cokernel is free abelian.

Consequently any unital C*-algebra containing a unital copy of an NCCW
complex covered by this 2-saturated tower criterion kills `alpha`.  A
surviving coefficient for Problem LXXVI must avoid this much larger
finite-cell class, not only one-dimensional dimension-drop blocks.
