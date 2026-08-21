---
rg: 2
id: finite-packet-central-sign-cannot-enforce-nonlinear-support
kind: claim
title: A finite packet cannot enforce nonlinear selector support on its whole marked central-sign sector
distinct_from:
  finite-selector-gadget-induction-barrier: that says every character of a finite abelian subgroup occurs in some representation of the ambient finite group; this records the marked-sector form needed by the threshold-free Fanizza groupifier and checks that gauge doubling does not remove the forbidden character.
  low-dimensional-hyperoctahedral-packet-groupifies-any-predicate: that excludes forbidden characters only below a dimension threshold; this proves why that threshold or an additional selected-type projection is essential.
  threshold-free-reverse-kleene-fanizza-red-team-audit: that gives the three-point multiplicative-shadow counterexample before auxiliary packets; this shows that every finite central-sign packet still has an exact marked forbidden-sector counterrepresentation.
---

Let `K` be a finite group, let `J in Z(K)` have order two, and let

```text
A=<J,d_1,...,d_k> <= K
```

be abelian.  Regard the signs of the `d_i` as Boolean selector values.  Then
for every character

```text
chi:A->{+1,-1},             chi(J)=-1,                 (FCS1)
```

there is an irreducible unitary representation `pi_chi` of `K` such that

```text
pi_chi(J)=-I                                                   (FCS2)
```

and the joint `A`-spectrum of `pi_chi` contains `chi`.  Consequently the
union of the selector spectra over **all** irreducible marked
`J=-1` representations of `K` is the full set

```text
{chi in dual(A): chi(J)=-1}.                             (FCS3)
```

In particular, no finite packet can enforce a proper nonlinear allowed set
of selector assignments on its entire `J=-1` sector.  A surviving central
sign is not a qualitative replacement for a selected irreducible-type
projection or for the dimension cutoff in the low-dimensional
hyperoctahedral packet.

## Proof

Fix `chi` as in `(FCS1)` and form the finite-dimensional induced
representation

```text
Ind_A^K chi.
```

Choose an irreducible constituent `pi_chi` in which the inducing copy of
`chi` occurs.  Equivalently, Frobenius reciprocity gives

```text
Hom_A(chi, Res_A^K pi_chi) != 0.                         (FCS4)
```

Because `J` is central in `K`, Schur's lemma makes `pi_chi(J)` scalar.  On
the nonzero `chi`-weight space from `(FCS4)` that scalar is `chi(J)=-1`, so
`pi_chi(J)=-I`.  The same weight space has selector values
`chi(d_1),...,chi(d_k)`.  This proves `(FCS2)--(FCS3)`.

The statement is stable under direct products, semidirect products, and
adding further finite packet coordinates: apply the same induction argument
to the enlarged finite group and the same marked abelian selector subgroup.

## Exact replay of the three-point counterexample

Take the nonlinear context

```text
R={(+1,+1),(+1,-1),(-1,+1)},                            (FCS5)
```

which forbids only `(-1,-1)`.  Let `d_x,d_y` be the two selector
involutions.  The character

```text
chi(J)=-1,       chi(d_x)=chi(d_y)=-1                  (FCS6)
```

induces an exact finite-dimensional representation of every finite packet
containing the marked abelian subgroup in which `J=-I` and the forbidden
joint atom is nonzero.  Thus adjoining a finite packet does repair the
`C^3` multiplicative shadow only **after** one selects a favorable central
idempotent `q_rho`; it cannot repair it unconditionally on the group-word
mark `J`.

## Gauge doubling does not remove the counterrepresentation

Replace each logical selector by two commuting shares

```text
d_x=A_x B_x,             d_y=A_y B_y.                  (FCS7)
```

and let the finite incidence-gauge group flip both shares by the central
sign:

```text
(A_x,B_x)->(J A_x,J B_x),
(A_y,B_y)->(J A_y,J B_y).                              (FCS8)
```

Choose a character of the abelian share subgroup with `chi(J)=-1` and, for
example,

```text
chi(A_x)=-1, chi(B_x)=+1,
chi(A_y)=-1, chi(B_y)=+1.                              (FCS9)
```

Both logical products in `(FCS7)` equal `-1`.  Under every gauge flip in
`(FCS8)`, the two signs of a share pair change together, so their product is
unchanged.  Hence the entire gauge orbit of `chi` still has the forbidden
logical assignment `(-1,-1)`.  Inducing this character to the finite
gauge-extended packet gives an exact marked representation whose whole
selector orbit is forbidden.  Gauge covariance is therefore a completeness
and reset symmetry, not an unconditional nonlinear-support selector.

## Consequence for threshold-free Fanizza groupification

The qualitative target `(FTFK2)` quantifies over every homomorphism into a
tracial matrix ultraproduct.  Exact finite-dimensional homomorphisms are a
special case.  Therefore a compiler assembled from finite context packets
whose only common retained carrier is a central word `J` cannot establish
`(FTFK2)`: the representation above is already an exact finite-dimensional
marked countermodel at one forbidden context.

There are only two exits within the finite-packet architecture.

1. Use a rational group-algebra type projection such as `q_rho` as the
   marked carrier.  This defeats the local induction countermodel, but then
   one must identify the selected carriers across noncommuting contexts;
   incidence-by-incidence stable letters do not supply one common joint
   carrier.
2. Add a genuinely infinite, matrix-only actuator which forces type
   selection or common-carrier coherence.  Threshold-free compactness
   removes the need for a numerical modulus, but not this semantic step.

Thus the exact remaining obstruction is not quantitative packet stability.
It is the construction of a **shared selected-type carrier across all native
Fanizza contexts** without identifying their selector algebras and thereby
classicalizing the BCS.

## Claim boundary

This is a no-go only for unconditional finite-packet support enforcement via
a common central sign.  It does not rule out a group-algebra mark, an
infinite proper-corner actuator, or another finite-dimensional-only
common-carrier mechanism.  It proves that neither larger finite packets nor
gauge doubling alone can realize the threshold-free groupifier.
