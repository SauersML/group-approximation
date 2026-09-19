---
rg: 2
id: stw99-lxxvi-higher-cell-obstruction-sequence-proof
kind: route
title: Use the loop-space fibre of cell restriction and iterate the stable even-degree vanishing
target: stw99-lxxvi-higher-nccw-s6-obstruction
requires:
  - stw99-lxxvi-one-dim-nccw-s6-criterion
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

## The exact sequence for one cell attachment

Apply `M_2` and unitary groups to `(CP)`.  Restriction

```text
Map(D^k,U(M_2(F))) -> Map(S^(k-1),U(M_2(F)))
```

is a fibration because the sphere inclusion is a CW cofibration.  Therefore
the strict pullback unitary group is also the homotopy pullback, and its
projection to `U(M_2(B))` has fibre over the identity

```text
Map((D^k,S^(k-1)),(U(M_2(F)),1))
 ~= Omega^k U(M_2(F)).                                 (1)
```

The long exact sequence contains

```text
pi_6(U(M_2(B))) --boundary_k--> pi_(5+k)(U(M_2(F)))
 -> pi_5(U(M_2(A))) -> pi_5(U(M_2(B))).                (2)
```

The last arrow sends `alpha_A` to `alpha_B`.  Thus nonzero survival in `B`
forces survival in `A`.  If `alpha_B=0`, exactness supplies a preimage

```text
xi in pi_(5+k)(U(M_2(F)))
```

of `alpha_A`.  Two choices differ by the image of `boundary_k`, so the class
of `xi` in the cokernel `(O)` is well defined.  Exactness also says that this
coset is zero exactly when `alpha_A` is zero, proving `(E)`.

More precisely, exactness makes the induced map

```text
coker(boundary_k) -> pi_5(U(M_2(A)))
```

injective.  It carries the obstruction coset to `alpha_A`.  The latter is
the image of the order-two class `alpha`, so `2 alpha_A=0`; injectivity gives
`2 omega_k(alpha;theta)=0`.  Therefore a cokernel with no nonzero
two-torsion forces the obstruction to vanish.  For an abelian group `G` and
a subgroup `L`, the quotient `G/L` has no nonzero element annihilated by two
exactly when `L` is 2-saturated in `G`, proving `(2S)`.

To identify `xi` geometrically, choose a based null-homotopy of the scalar
class in `U(M_2(B))`.  Its image under the attaching map is a family on
`S^5 times I times S^(k-1)`.  Glue this to the constant scalar family on
`S^5 times D^k`.  Collapsing the based boundary gives a map

```text
S^(5+k)->U(M_2(F)).                                    (3)
```

Changing the null-homotopy by an element of `pi_6(U(M_2(B)))` changes (3)
by its image under `boundary_k`, exactly as the cokernel records.

## The stable odd-cell class

Write `F=directSum_j M_(d_j)`.  If `k` is odd and `5+k<4d_j`, the standard
unitary stable range gives

```text
pi_(5+k)(U(2d_j))=pi_(5+k)(U).
```

The degree `5+k` is even, so Bott periodicity makes this group zero.  Hence
the middle-left group in (2) vanishes and a zero scalar class at the previous
skeleton remains zero after the attachment, for every attaching map.

At the zero-skeleton, all `r_i>=2` kill the scalar class by the exact
one-dimensional NCCW calculation's evaluation argument (equivalently by
finite matrix amplification).  Induction over a finite tower of odd cells
satisfying `(SR_k)` therefore proves the positive class.

For an even-dimensional stable cell, `5+k` is odd and the target in (2) is
free abelian (one copy of `Z` for each matrix summand of `F`).  The scalar
class can therefore survive only if the connecting image is not 2-saturated:
the quotient must acquire order-two torsion.  If the source `pi_6` vanishes,
the cokernel is itself free, so even this cell preserves vanishing for every
attaching map.  In a tower, the same argument iterates whenever every
connecting image is 2-saturated.  Thus stable range gives a parity-free
one-stage theorem, while later even cells require only a lattice-saturation
calculation rather than an unrestricted integer obstruction.
