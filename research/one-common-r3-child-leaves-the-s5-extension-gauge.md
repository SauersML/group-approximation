---
rg: 2
id: one-common-r3-child-leaves-the-s5-extension-gauge
kind: claim
title: One authenticated R3 child leaves the shared-S5 extension gauge intact
invalidates:
  - authenticate-one-r3-child-closes-mixed-seam
distinct_from:
  shared-endpoint-r2-r3-anchor-has-linear-seam-bound: that assumes both the coarse parent and complementary child are common, and then cancels them; this shows the child alone merely transports the mismatch to the two still-private parents.
  common-pivot-r2-r3-data-preserve-a6-label-swap: that diagonally lifts the finite A6 label-swap model and keeps all R3 data contextual; this fixes one child literally across the two extensions and exhibits the residual multiplicity rotation on the other child.
  shared-s5-gauge-is-invisible-to-all-r4-r5-cells: that proves disjoint-support commutator energies cannot see the extension gauge; this treats the remaining overlapping-support R3 alternative.
---

Let `X_0,X_1,D,C_0,C_1` be unitaries satisfying two private R3 splits with
one literally common complementary child:

```text
C_a=X_a D,                         a=0,1.                       (OCR1)
```

Then

```text
||X_0-X_1||_2=||C_0-C_1||_2.                                  (OCR2)
```

Thus authenticating `D` alone pays none of the seam: it transfers the entire
missing-child mismatch isometrically to the coarse parents.  If one also
authenticates a common parent `C`, then cancellation gives
`X_0=X_1`; that is exactly the already-established R3 anchor theorem, not a
way to obtain its hypotheses.

There is an exact finite-dimensional shared-S5 gauge witnessing the missing
hypothesis.  Split the six letters

```text
Omega={i,p,j,k,l,q}
```

into two layers `Omega_0,Omega_1`.  On `C^(Omega_0 disjointUnion Omega_1)`
let

```text
H_0=Sym({p_0,j_0,k_0,l_0,q_0}),
H_1=Sym({p_1,j_1,k_1,l_1,q_1}),       K=H_0 directProduct H_1,
X=(i_0 p_0),                    D=(i_1 p_1),
C=XD.                                                            (OCR3)
```

Let `v_0` be the normalized all-ones vector on the five-point `H_0` orbit,
and let `U` swap `e_(i_0)` with `v_0`, acting identically on their orthogonal
complement and on the whole second layer.  Then

```text
U in rho(K)' intersection {rho(D)}',
X_1=UXU^* != X_0=X,
D_1=D_0=D,
C_a=X_aD.                                                        (OCR4)
```

Both contextual split relations are exact.  Their common diagonally lifted
S5 face is contained in `K` and is therefore literal (in fact the larger
product face `K` is literal),
and the complementary child is literally the same operator, yet the other
child and coarse parent differ.  Amplifying this fixed packet gives the same
positive normalized-HS mismatch in arbitrary multiplicity.

The approximate identity is equally sharp.  If

```text
||C_a-X_aD||_2<=eta_a,
```

then

```text
abs(||X_0-X_1||_2-||C_0-C_1||_2)<=eta_0+eta_1.                  (OCR5)
```

Hence no estimate using private R3 defects and one authenticated child can
control the seam unless it separately controls the parent mismatch.  A live
mixed-R3 route must authenticate **both** the coarse parent and the
complementary child; at that point the desired arm comparison is immediate
unitary cancellation.
