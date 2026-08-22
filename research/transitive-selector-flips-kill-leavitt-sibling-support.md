---
rg: 2
id: transitive-selector-flips-kill-leavitt-sibling-support
kind: claim
title: Transitive four-sector flips globalize the gauge only by killing Leavitt sibling support
distinct_from:
  leavitt-crossed-gram-pauli-charge-has-sectorwise-escape: that gives the sectorwise gauge absorber and the positive common-packet inequality; this tests the smallest packet flips intended to turn the four sectors into one irreducible type.
  tensor-independent-child-carrier-gap: that pays after one common carrier is recovered in both child algebras; this proves that the natural selector actor cannot recover it without violating exact sibling orthogonality.
  d16-charge-of-two-leavitt-branches-is-collapse-or-zero: that compares the two partial-swap words and either identifies their child ranges or sees trivial returns; this treats the actor orbit on the four joint range sectors.
---

# Transitive four-sector flips globalize the gauge only by killing Leavitt sibling support

ESTABLISHED.  Let `F_0,F_1` be commuting range projections and write their
four joint atoms as

```text
E_(ab)=F_0^a(1-F_0)^(1-a) F_1^b(1-F_1)^(1-b),
a,b in {0,1}.                                             (TSF1)
```

The sectorwise Pauli escape places an independent multiplicity gauge on the
overlap atom `E_(11)=F_0F_1`.  The smallest proposed repair adjoins the two
bit flips

```text
(a,b) -> (a+1,b),             (a,b) -> (a,b+1),          (TSF2)
```

or any packet actor transitive on the four atoms.  In every exact unitary
representation of these covariance relations, conjugate projections have
equal rank and trace.  Hence

```text
tau(E_00)=tau(E_10)=tau(E_01)=tau(E_11).                 (TSF3)
```

This does make the packet type irreducible enough for Schur's lemma to leave
one global multiplicity pair.  The crossed-Pauli computation then gives, for
`alpha=tau(E_11)` and every global gauge commutator `K`,

```text
|| (1-2E_11) tensor K-1 ||_2^2 >=4alpha
                         (alpha<=1/2).                   (TSF4)
```

But exact Leavitt siblings satisfy

```text
E_11=F_0F_1=0                                            (TSF5)
```

while the two child ranges are nonzero.  Equations `(TSF3)--(TSF5)` force
all four atoms, hence the whole parent carrier, to vanish.  Therefore the
transitive repair destroys the nonzero exact Leavitt completeness model.
The same conclusion holds for any finite actor whose orbit contains the
overlap atom and either allowed child atom; equality of ranks already
propagates zero from the overlap to that child.

The maximal completeness-preserving flip is the sibling exchange

```text
E_10 <-> E_01.                                           (TSF6)
```

It realizes the native binary branch symmetry and preserves the common
central Pauli sign.  However `E_11` is then a separate actor orbit (as is
`E_00`), so its multiplicity gauge remains independent and the exact
sectorwise cancellation model survives.  Adding Pauli partners only on the
two allowed siblings locks their gauges to one another, not to the forbidden
overlap gauge.

Thus no selector permutation packet on the native four-sector chart has all
three desired properties:

1. preserve nonzero orthogonal Leavitt siblings;
2. connect the overlap sector to the sibling sectors; and
3. force one global multiplicity gauge for the crossed-Pauli charge.

To use the positive inequality `(TSF4)`, the compiler must connect gauges by
a relation which is not rank-preserving transport of the selector atoms--for
example a same-source Gram row or a one-sided proper-corner incidence.  A
larger transitive finite packet only repeats the rank obstruction.

