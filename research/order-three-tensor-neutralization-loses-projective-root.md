---
rg: 2
id: order-three-tensor-neutralization-loses-projective-root
kind: claim
title: Cubing an order-three projective tuple forgets its multiplier and ordinary HS correction cannot recover a projective tensor root
distinct_from:
  deligne-sector-gap-is-exactly-nonhyperlinearity: that identifies the uniform mod-three projective defect gap with non-hyperlinearity of Deligne's triple cover; this rules out a proposed route from ordinary stability of a cocycle-neutral tensor power to that gap.
  sl3-regular-projective-correction-is-inner-adjoint-stability: that identifies the inner-adjoint locus needed to invert adjoint correction; this gives the parallel order-three tensor-power loss and an explicit exact Weyl model showing that cocycle neutralization forgets the Schur class.
  fixed-rank-index-authenticator-has-gap-or-functoriality: that gives the general normalized-HS discontinuity of determinant and index readouts; this applies it to the mod-three projective sector and separates exact divisibility from a defect gap.
---

Let `G` be a group, let `alpha:G x G -> mu_3` be a normalized multiplier,
and suppose a tuple `U_g in U(d)` is an `alpha`-projective
`delta`-representation on a fixed finite multiplication window:

```text
||U_g U_h-alpha(g,h)U_(gh)||_(2,d) <= delta.           (OTN1)
```

The diagonal third tensor power is an ordinary approximate representation:

```text
T_g=U_g tensor U_g tensor U_g,
||T_g T_h-T_(gh)||_(2,d^3) <=3 delta.                  (OTN2)
```

Indeed `alpha(g,h)^3=1`, and the tensor telescoping inequality gives the
factor `3`.  Thus tensor cubing removes the projective phase before any
Kazhdan or stability argument is applied.

This operation has no converse supplied by ordinary normalized-HS
stability.  Such stability can replace the tuple `T_g` by an arbitrary
genuine representation on `C^(d^3)`.  It does not assert that the corrected
representation remains in the nonlinear diagonal-cube locus

```text
{ V tensor V tensor V : V in U(d) },                  (OTN3)
```

and it supplies no projective tensor root close to the original `U_g`.
The loss is already exact.  For `G=C_3 x C_3`, let `X,Z in U(3)` be the
Weyl shift and clock, with `ZX=omega XZ`, and put

```text
pi(a,b)=X^a Z^b.
```

Then

```text
pi(a,b)pi(c,e)=omega^(b c) pi(a+c,b+e),               (OTN4)
```

and the commutator bicharacter is nontrivial, so the multiplier in `(OTN4)`
is not a coboundary.  Nevertheless `pi^(tensor 3)` is an exact ordinary
representation.  Hence exactness, let alone correctability, of the cubed
tuple does not remember whether the original multiplier is trivial.  Any
positive theorem recovering an `alpha`-projective root would be an
additional projective-stability theorem, not a consequence of ordinary
stability of `G`.

The adjoint variant loses at least as much information.  `Ad(U_g)` cancels
every scalar multiplier, but an ordinary exact correction on the Hilbert
space `M_d` need not act by algebra automorphisms and need not have the form
`Ad(V_g)`.  This is exactly the inner-locus obstruction isolated in
`sl3-regular-projective-correction-is-inner-adjoint-stability`.

Finally, determinants do not restore the missing inverse.  In an exact
`d`-dimensional projective representation, taking determinants only proves
that `d[alpha]=0`; for an order-three class this gives the divisibility
condition `3|d`, not a normalized-HS defect floor.  Moreover

```text
W_d=exp(i theta/d) I_d,
||W_d-I_d||_(2,d) ->0,       det(W_d)=exp(i theta),    (OTN5)
```

so determinant phase is discontinuous in normalized HS norm.  Relator
determinant identities and the nontriviality of the Deligne class therefore
classify exact finite-dimensional sectors only.  They cannot promote
Deligne finite-dimensional invisibility to the dimension-uniform Maslov
gap.

**Deligne consequence.**  For the nontrivial mod-three multiplier of
`Sp_4(Z)`, tensor cubing or adjointing may be used only after one proves an
extra inner/tensor-root projective correction theorem.  Property `(T)`,
ordinary or flexible HS correction of the neutralized tuple, cohomological
order mismatch, and determinant consistency do not by themselves prove
`maslov-mod3-projective-defect-gap`.
