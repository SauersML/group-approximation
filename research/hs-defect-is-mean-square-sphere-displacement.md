---
rg: 2
id: hs-defect-is-mean-square-sphere-displacement
kind: claim
title: A unitary microstate is exactly a mean-square almost action on the sphere
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

**Identity.**  For `U, V ∈ U(d)` and `x` uniform on the unit sphere of `C^d`,

```text
E_x ‖Ux - Vx‖^2  =  (1/d)‖U-V‖_F^2  =  d_2(U,V)^2.
```

(Immediate: `E_x⟨Mx,Mx⟩ = (1/d)tr(M^*M)` for uniform `x`, applied to
`M = U-V`.)

**Consequence — the recoding.**  A finite unitary microstate is *literally* a
finite family of isometries of a homogeneous metric measure space that is an
almost action in mean-square transport cost:

```text
E_x ‖U_g U_h x - U_{gh} x‖^2 = d_2(U_g U_h, U_{gh})^2  ≪ 1   on tested products,
E_x ‖U_g x - U_h x‖^2        = 2 - 2 Re tau(U_g^* U_h)       on tested pairs,
```

so the multiplicative defect is a transport cost and regular-trace separation
is *macroscopic geometric separation*: `tau(U_w) ≈ 0` for a nontrivial tested
word says `E‖U_w x - x‖^2 ≈ 2`, i.e. a typical point is moved essentially as
far as the geometry allows.  Freeness becomes an anti-collision statement on
`S^{2d-1}`.

**Why record it.**  Nothing here is deep; what it buys is a change of
category.  Every extraction technique in this graph so far reads a microstate
as an operator-algebraic object (a masa to find, a commutant to normalize, a
block structure to monomialize).  This identity says the same data is a
quantization problem in geometry and probability, whose finite-model target —
a labelled Schreier graph on a point cloud — is indexed by a *geometric
codebook* rather than by a finite subset of the group.  That is the precise
sense in which the design route of `geometric-schreier-design` has no a priori
Følner term to pay, which is what makes it worth separating from the
amenable-extraction paradigm.

**Scope limit.**  The identity is about *positions*, and Hamming distance is
about *indices*: two selected sample points can be geometrically arbitrarily
close and still count as a full unit of Hamming disagreement.  Nothing in this
claim closes that gap; it only states the input hypothesis that the design
conjecture consumes.

Source: `research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md` §8.
