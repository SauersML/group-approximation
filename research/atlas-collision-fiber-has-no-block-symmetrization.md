---
rg: 2
id: atlas-collision-fiber-has-no-block-symmetrization
kind: claim
title: Packet energy has no averaging principle from the full collision fiber to repeated S3 blocks
distinct_from:
  atlas-repeated-collision-fiber-is-two-block-procrustes: that exactly optimizes after imposing a repeated U(3) by U(3) block; this proves symmetry does not justify imposing that block.
  atlas-a4-packet-commutant-synchronization: that rounds an operator already known to commute with every packet letter into the A8 commutant; here the collision-fiber variable is not approximately central and its objective is nonlinear.
  finite-group-shared-overlap-polar-alignment: that polar-repairs an averaged almost-intertwiner with a quantitative lower support bound; here the natural symmetry average can be exactly zero.
---

Let `E_pkt(U)` be the sum of the thirty squared normalized
Hilbert--Schmidt defects of the stored A4 packet, with the second-chart letters
represented by `U rho(g) U^*`.  Let

```text
F_c={U unitary: U^*rho(b_0)U=c}                       (SYM1)
```

be one exact collision conjugator fiber.

There is no symmetry/Jensen argument reducing the minimization of `E_pkt` on
`F_c` to the repeated `Reg(S3)` block algebra.

First, the unitary group on the `3360` multiplicity copies commutes with the
local subgroup `K~=S3`, but it does not commute with the other packet letters.
The ten packet letters generate `A8`.  Hence

```text
rho(K)' intersect intersection_(s in S_pkt) rho(s)'
 =rho(A8)'.                                           (SYM2)
```

In particular the full `K`-copy group is not a symmetry of the packet
objective.  Conjugating or multiplying a collision lift by a generic copy
unitary changes the fixed coefficients outside `K`, so Haar averaging over
that group cannot be combined with invariance of `E_pkt`.

Second, the objective has no ambient convexity which could replace invariance.
Extend the same word formula polynomially to arbitrary matrices `X`, replacing
each second-chart letter by `X rho(g) X^*`.  For the exact reference packet
alignment `R`,

```text
E_pkt(R)=E_pkt(-R)=0,                                 (SYM3)
```

because scalar phase cancels from every conjugated letter.  At their midpoint
`X=0`, every packet word product is zero, since each word contains a
second-chart syllable.  Therefore every normalized squared defect equals one:

```text
E_pkt(0)=30 > (E_pkt(R)+E_pkt(-R))/2.                 (SYM4)
```

Thus even the natural polynomial extension is nonconvex.

Finally this same phase supplies an obstruction inside every collision fiber.
For `U in F_c`, the whole circle `zU` lies in `F_c` and has the same packet
energy, while

```text
integral_(z in T) zU dz=0.                            (SYM5)
```

The polar factor at zero is undefined.  Any unitary completion is arbitrary
and has no collision or packet-energy monotonicity.  Hence an
average-then-polar argument requires an additional nonzero-overlap/support
estimate not supplied by collision 19243 or packet symmetry.

The genuine coefficient symmetry `rho(A8)'` does not repair the proposed
reduction.  Its action which preserves the fixed collision fiber is left
multiplication, and that is exactly the action with zero phase barycenter in
`(SYM5)`.  Conjugation averaging would instead land in its fixed algebra
`rho(A8)''`, the left group algebra, but generally moves `c` to `D c D^*` and
does not preserve `(SYM1)`; even if it did, its fixed algebra is not the
repeated six-dimensional `U(3) x U(3)` block.  Therefore the exact Procrustes
slice cannot be promoted to a global `k=1`, let alone all-`k`, minimization
theorem by regular symmetry alone.
