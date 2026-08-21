---
rg: 2
id: selector-edge-type-support-is-twist-invariant
kind: claim
title: A selector-free common edge type sees whole affine twist orbits of assignments
distinct_from:
  finite-packet-central-sign-cannot-enforce-nonlinear-support: that uses induction from the whole marked selector subgroup and obtains every marked assignment; this quantifies exactly how much selector information a common edge type must retain.
  selector-free-spin-reset-leaves-contexts-independent: that gives an exact finite reset countermodel for one Schur incidence; this is a general representation-theoretic twist obstruction and applies directly to the selector-correlated router packet.
  gauge-doubling-gives-selector-flip-symmetries: that supplies completeness-preserving gauge symmetries; this proves that gauge doubling does not lower the logical selector rank which a type-selecting edge must carry.
---

Let `L` be a finite group, let `A<=L` be an elementary abelian selector
subgroup, let `E<=L`, and fix `sigma in Irr(E)`.  Put

```text
X_E={chi in Hom(L,{+1,-1}): chi|_E=1},
H_E={chi|_A: chi in X_E} <= dual(A).                    (SET1)
```

Let `R_sigma` be the union of the `A`-weights occurring in irreducible
representations `pi of L` for which

```text
Hom_E(sigma,Res_E^L pi) != 0.                           (SET2)
```

Then

```text
R_sigma H_E=R_sigma.                                    (SET3)
```

Thus an `E`-type can select assignment support only as a union of affine
`H_E`-orbits.  In particular, if every selector character extends to `L`
trivially on `E`, then a nonempty `E`-type sees **every** assignment.

## Proof

For `chi in X_E`, tensoring by `chi` permutes `Irr(L)` and

```text
Res_E(pi tensor chi)=Res_E(pi).
```

Hence `(SET2)` holds for `pi` if and only if it holds for `pi tensor chi`.
The `A`-weight set of the latter is the weight set of `pi` multiplied by
`chi|_A`.  Taking the union over all irreducibles above `sigma` proves
`(SET3)`.

Equivalently, the central support in `C[L]` of the primitive `E`-type
projection has selector spectrum invariant under `H_E`.  This formulation
applies whether the carrier is described by a central idempotent, a finite
matrix-unit packet, or the isotypic range after finite-group exactification.

## Direct-product selector packets

For the local correlated-router architecture, the finite group before the
router relation has the form

```text
L=P times A,                                             (SET4)
```

where `P` contains the finite truth packet and `A` is the actual commuting
context-selector group.  If a proposed common reset/edge subgroup satisfies

```text
E<=P times B,                B<=A,                      (SET5)
```

then every character in the annihilator `B^perp` extends trivially over `P`
and lies in `X_E`.  Consequently selected support must be a union of
`B^perp`-cosets.  If the selected packet is required to have joint support
**exactly** the desired allowed set `R subseteq dual(A)`, as in the common
hyperoctahedral type, this forces

```text
B^perp <= Stab(R),
rank(B) >= rank(A)-rank(Stab(R)).                        (SET6)
```

Here `Stab(R)={h:R+h=R}` is the translation stabilizer of the truth table.

## Exact ranks for the Fanizza nonlinear menu

Write Boolean signs additively over `F_2`.  The three nonlinear shapes in
`fanizza-final-bcs-has-fixed-nonlinear-menu` have the following translation
stabilizers (the allowed and forbidden sets have the same stabilizer):

```text
C13/C14:  F={(1,0,1),(0,1,1)},
          Stab(F)=< (1,1,0) >,              rank bound 2;

C17:      F={(1,0,0),(1,0,1),(1,1,0),(0,1,1)},
          Stab(F)=0,                        rank bound 3;

C18:      F=A_123 times A_456,
          Stab(F)=0 times A_456,            rank bound 4,              (SET7)
```

where `A_456` is the two-dimensional even-parity subspace from `(FNM1)`.
For `C17`, for example, translating the first listed atom by each of the
three differences to the other listed atoms fails to preserve the remaining
set, so the stabilizer is trivial.  The five-element set `A_123` has trivial
translation stabilizer because every nontrivial translation orbit has even
cardinality, while `A_456` is itself a subgroup.

Therefore any finite edge type whose joint spectrum is the full `C17`
allowed support must retain all three independent logical selector
directions.  No selector-free common spin type can exclude even one
assignment: in that case `H_E=dual(A)` and every nonempty selected support is
the whole cube.

## Gauge doubling does not lower the bound

Under gauge doubling, replace `A=F_2^r` by the share space

```text
A'=F_2^(2r),       ell:A'->A,
ell(a_1,b_1,...,a_r,b_r)=(a_1+b_1,...,a_r+b_r).         (SET8)
```

The lifted truth set is `R'=ell^(-1)(R)`, and

```text
Stab(R')=ell^(-1)(Stab(R)).                             (SET9)
```

Hence

```text
rank(A')-rank(Stab(R'))
 =rank(A)-rank(Stab(R)).                                (SET10)
```

The private gauge orientations enlarge the invisible stabilizer by exactly
`ker(ell)`; they do not remove one logical direction from the common type.
In particular a `C17` type-selecting edge still has to carry rank three of
logical selector information after gauge doubling.

## Consequence for the shared selected-type carrier

Canonical Plancherel mass can select a favorable local type once its rational
idempotent is named.  It cannot make a selector-free reset type distinguish
nonlinear support: twist-equivalent favorable and forbidden types occur at
the same edge.  Any finite-incidence construction must therefore either

1. carry at least the ranks in `(SET7)` through its common edge and control
   the resulting noncommuting context holonomy; or
2. use an infinite/block-escaping algebraic corner or a genuinely matrix-only
   actuator.

This explains categorically why common symplectic spin reset and gauge
covariantization solve completeness and scale matching but not selected-type
alignment.

## Claim boundary

The theorem does not say that carrying the full selector quotient is
impossible.  It proves that a common type which forgets every selector
direction cannot exclude a forbidden assignment, and gives the exact minimum
ranks for the full-support packet realization used by the current
hyperoctahedral atlas.  A smaller union of affine cosets contained in the
allowed set may require fewer directions, but would need a separate global
completeness and overlap-balancing argument.
