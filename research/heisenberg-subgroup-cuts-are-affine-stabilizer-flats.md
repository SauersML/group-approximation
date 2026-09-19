---
rg: 2
id: heisenberg-subgroup-cuts-are-affine-stabilizer-flats
kind: claim
title: Subgroup spectral cuts in a Heisenberg spin sector are exactly affine stabilizer flats
distinct_from:
  canonical-finite-packet-data-stop-at-scalar-overlaps: that computes canonical scalar overlaps and leaves arbitrary external multiplicity rotations; this classifies the projections literally nameable by Pauli elements or subgroup-character data inside one multiplicity-free spin block.
  sectorwise-scalar-finite-group-words-are-selector-affine: that classifies group words acting scalarly across central selector sectors; this classifies joint eigenspace projections of arbitrary Pauli subgroups inside one fixed central sector.
  twisted-regular-predicate-projections-have-positive-trace: that proves every nonzero predicate idempotent survives in a twisted regular representation; this determines exactly which such idempotents can be a single subgroup-character cut in an irreducible Heisenberg representation.
---

Let `E` be an extraspecial `2`-group with center `<J>`, let

```text
V=E/<J> isomorphic to F_2^(2n),
```

and let `pi` be the irreducible representation with `pi(J)=-I` on a
`2^n`-dimensional space.  For a subgroup `A<=E` and a one-dimensional
character `chi` of `A`, let

```text
P_(A,chi)={xi: pi(a)xi=chi(a)xi for every a in A}.       (HSC1)
```

If this joint eigenspace is nonzero, the image `W=A<J>/<J>` is isotropic for
the commutator symplectic form.  Writing `r=dim_F2 W`, one has

```text
rank(P_(A,chi))=2^(n-r),
tr_(2^n)(P_(A,chi))=2^(-r).                              (HSC2)
```

After removing the redundant central element, its orthogonal projection is
the stabilizer idempotent

```text
p_(W,chi)=2^(-r) sum_(w in W) conjugate(chi(w)) pi(w).   (HSC3)
```

The Pauli matrices `pi(w)` are linearly independent.  Consequently two
nonzero cuts `(HSC3)` are equal if and only if their isotropic subspaces and
characters agree.  In a maximal commuting context, whose atoms are indexed
by the characters of a Lagrangian `L<=V`, a coarse diagonal projection

```text
p_S=sum_(lambda in S) p_lambda
```

is a single subgroup-character cut exactly when `S` is an affine flat in
`L^*` (a coset of an annihilator).  In particular:

1. a nontrivial spectral cut of one Pauli group element is balanced, of
   normalized trace `1/2`;
2. literal subgroup-character data expose only traces `2^(-r)`; and
3. sharing such data between two Heisenberg charts can identify only the
   same affine stabilizer flat, not an arbitrary union of context atoms.

Hence attaching unique-central-character Heisenberg packets to equal-atom
contexts cannot by literal shared Pauli elements or subgroup eigenspace data
encode a dense dyadic projection lattice.  For example, a union of three
atoms in an eight-atom context has trace `3/8` and is not one such cut.  More
generally the trace set `{2^(-r)}` is not dense in `[0,1]`.

This is a fence only for the proposed literal-sharing language.  Boolean
sums of stabilizer cuts, non-Pauli overgroups, or a separate group-algebra
projection transport compiler are not ruled out by this classification.
For the smallest Boolean-sum witness, however,
`three-of-eight-transport-forces-chart-conjugacy` proves that one literal
group-word transporter can move the three-atom projection only by conjugating
the whole context and affinely permuting all eight atoms.  Thus the remaining
escape needs genuinely additive/piecewise group-algebra transport, not merely
one more shared or conjugating group element.
