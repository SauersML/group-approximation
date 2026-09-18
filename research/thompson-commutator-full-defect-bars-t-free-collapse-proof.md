---
rg: 2
id: thompson-commutator-full-defect-bars-t-free-collapse-proof
kind: route
title: Compress an interval subgroup of F' by a dyadic PL map, move an endpoint by a disjoint centralizer, and use simplicity of F' and amenable-implies-MF
target: thompson-commutator-full-defect-bars-t-free-collapse
requires:
  - thompson-f-rigid-interval-subgroups-facts
  - amenable-implies-operator-mf
artifacts:
  - experiments/thompson-full-defect-2026-09-17/check_defect.py
---

Notation is that of the target.  Imported facts come from
`thompson-f-rigid-interval-subgroups-facts`:

- (F1) `F'` is simple and consists of the elements with support in `(0,1)`;
- (F2) `F[a,b]` is isomorphic to `F` for dyadic `a<b`.

`amenable-implies-operator-mf` gives that every countable amenable group
is MF.

## Step 0: the elements

All maps are piecewise linear with dyadic breakpoints and slopes that are
powers of 2, so they lie in `F`.

- **`u`.**  Its breakpoints are `(0,0), (1/4,1/4), (1/2,3/8), (5/8,5/8),
  (1,1)`, with slopes `1, 1/2, 2, 1`.  It is the identity near `0` and near
  `1`, so `u` lies in `F'` by (F1).
- **`x_0`.**  Its breakpoints are `(0,0), (1/2,1/4), (3/4,1/2), (1,1)`.  It
  moves every point of `(0,1)`.
- **`c` and `l`.**  For dyadic `a<b`, the affine map `x -> a+(b-a)x`
  conjugates `F` onto `F[a,b]` extended by the identity.  Let `c` be the copy
  of `x_0` on `[1/2,5/8]` and `l` the copy on `[3/8,1/2]`.  Their open
  supports are exactly `(1/2,5/8)` and `(3/8,1/2)`, and both lie in `F'`.

## Step 1: compression

For any homeomorphism `g`, `g F[a,b] g^-1` is the set of elements of `F`
supported in `g[a,b]`, whenever `g` lies in `F`.  Since `u[1/4,1/2]=[1/4,3/8]`,
we get `u L u^-1 = F[1/4,3/8]`, which is contained in `L`.  The inclusion
is proper: `l'`, the copy of `x_0` on `[3/8,1/2]`, lies in `L` but moves
points outside `[1/4,3/8]`.  (That is `l` itself.)

## Step 2: the centralizing element

`c` fixes `[0,1/2]` pointwise and every element of `L` fixes `[1/2,1]`
pointwise.  Two homeomorphisms each supported in the fixed set of the other
commute, so `c` lies in `C_F'(L)`.

## Step 3: nontrivial defect

Put `d=u c u^-1`, which lies in `F'`.

- **`d(1/2)`.**  On `[1/2,5/8]`, `u(x)=3/8+2(x-1/2)`, so `u^-1(1/2)=9/16`.
  This is the image of the midpoint `1/2` under the affine chart of
  `[1/2,5/8]`, and `x_0(1/2)=1/4`, so `c(9/16)=1/2+(1/8)(1/4)=17/32`.
  Hence `d(1/2)=u(17/32)=3/8+2/32=7/16`.
- **`d(3/8)`.**  Here `u^-1(3/8)=1/2`, `c(1/2)=1/2` and `u(1/2)=3/8`, so
  `d(3/8)=3/8`.

The open support of `d l d^-1` is `d((3/8,1/2))=(3/8,7/16)`, which is
different from `(3/8,1/2)`, the open support of `l`.  Conjugate elements
with different open supports are different elements, so `d l d^-1` is not
`l`.  Hence `delta=[d,l]=d l d^-1 l^-1` is not the identity.

The script `experiments/thompson-full-defect-2026-09-17/check_defect.py`
checks with exact rationals that `u`, `c` and `l` are in `F` with the
stated supports, that `d(1/2)=7/16`, and that `delta` moves 111 of the 1025
points `k/1024`.  Every moved point lies in `(3/8,1/2)`.

## Step 4: full defect

`delta` is a generator of `D_F'(L)`, since `u`, `c` and `l` have the
required types.  So `D_F'(L)` is a nontrivial normal subgroup of `F'`, and by
(F1) it is all of `F'`.

For `F`, the same generator gives that `D_F(L)` contains the normal closure
of `delta` in `F`.  That closure contains the normal closure of `delta` in
`F'`, which is `F'`.  Conversely, every generator of `D_F(L)` is a
commutator, so `D_F(L)` lies in `F'`.  Hence `D_F(L)=F'`.

The remaining properties in item 2 are standard:

- `L` is isomorphic to `F` by (F2);
- `F'` is torsion-free as a group of PL homeomorphisms;
- `F'` has no finite quotients, being infinite and simple;
- `F'` is the increasing union of `F[2^-n,1-2^-n]` by (F1), and each of
  these is isomorphic to `F` by (F2), which is finitely presented.

## Step 5: barrier

Assume that `(F',L)` is in `P` and that (FDC_P) holds.  By Step 4,
`Rad_MF(F')=F'`.

- **`F'` is not MF.**  If it were, the identity would be an injective
  homomorphism to an MF group, so `Rad_MF(F')` would be trivial, which is
  impossible since `F'` is not trivial.
- **`F` is not MF.**  Restricting an embedding `F -> U(Q)` to `F'` would
  embed `F'`.
- **`F` is not amenable.**  `F` is countable, so if it were amenable it
  would be MF by `amenable-implies-operator-mf`.

This proves item 3.  Item 4 is item 3 read for `Delta`.  A proof of the
endpoint that uses only `D_Delta(L)=Delta`, together with properties that
`(F',L)` also has, is a proof of (FDC_P) for a `P` containing `(F',L)`.  By
item 3 it then proves that `F` is not amenable.

## Remark: the finitely generated version (not part of the claim)

Thompson's `T` contains `F` as the stabilizer of a point of the circle.  It
is simple, finitely presented and non-amenable (Cannon--Floyd--Parry;
not imported here).  So the same cell gives `D_T(L)=T`.  A collapse
restricted to finitely presented simple ambient groups, applied to `T`,
would prove that `T` is not MF.  The graph records no MF model of `T` or
`V`, and `hyperlinear-fp-simple-via-thompson-v` is OPEN.  The same goes for
`V`, which lies in the elementary group of the binary Leavitt algebra by
`leavitt-cylinder-swaps-generate-thompson-in-el`.
