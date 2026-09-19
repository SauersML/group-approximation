---
rg: 2
id: sp4-contains-no-isw-affine-subgroup
kind: claim
title: Sp4(Z) contains no standard Ioana--Spaas--Wiersma affine obstruction subgroup
distinct_from:
  sp4-maximal-parabolics-contain-no-isw-affine-subgroup: that excludes the affine subgroup only after it is already known to lie in a standard maximal parabolic; this proves every putative embedding is virtually forced into such a parabolic.
  isw-theorem-a-has-no-data-on-sp4-lattice: that rules out all scalar Theorem A input by finite-dimensional multiplier finiteness; this is an independent subgroup-classification statement and does not address operator-valued Theorem C data.
---

Let `F < SL_2(Z)` be a nonamenable free subgroup and let

```text
E = Z^2 rtimes F
```

use the standard action.  Then `E` does not embed in `Sp_4(Z)`.

Indeed, suppose that it embeds and write `A` for the image of `Z^2`.
Multiplicative Jordan decomposition is functorial on the commuting group
`A`, so

```text
psi:A -> Sp_4(Q),             psi(a)=a_s
```

is a conjugation-equivariant homomorphism.  The Zariski closure `D` of
`psi(A)` is diagonalizable.  Since `N(D)/Z(D)` is finite, a finite-index
subgroup `F_0 < F` centralizes `D`.  Choose a hyperbolic `f in F_0`.  Then

```text
psi((f-1)a)=1
```

for every `a in A`, and `(f-1)A` has finite index in `A`.  Consequently a
characteristic finite-index subgroup `A_0=mA` consists entirely of
unipotent elements.

Let `U` be the rational Zariski closure of `A_0` in `Sp_4`.  It is a
nontrivial unipotent group normalized by `A_0 rtimes F_0`.  On the natural
symplectic space `V=Q^4`, the common fixed space `W=V^U` is nonzero and
proper, rational, and preserved by `N(U)`.  If `dim W` is one or three,
`N(U)` preserves an isotropic line.  If `dim W=2` and `W` is isotropic,
`N(U)` preserves a Lagrangian.  The remaining case, a symplectic
two-dimensional `W`, is impossible: `U` acts nontrivially and unipotently
on the invariant symplectic complement `W^perp`, hence fixes a nonzero
vector there, contradicting `W=V^U` and `W cap W^perp=0`.

Thus `A_0 rtimes F_0` lies in a proper rational Klingen or Siegel
parabolic.  After rational conjugacy and arithmetic commensurability this
reduces to the integral parabolic case, which is excluded by
`sp4-maximal-parabolics-contain-no-isw-affine-subgroup` for every
finite-index nonamenable `F_0` and rank-two lattice `A_0`.

This closes the residual “genuinely global affine subgroup” shortcut in the
symplectic LLP audit.  It does not decide LLP: the only surviving published
refutation surface remains the operator-valued cocycle mechanism of ISW
Theorem C, while a positive proof still requires intrinsic LLP or an
equivalent lifting theorem.
