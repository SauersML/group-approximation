---
rg: 2
id: private-gauges-close-fanizza-triangle
kind: claim
title: Incidence-private gauges and a finite support menu close the exact Fanizza triangle torsors
distinct_from:
  fanizza-triangle-two-cell-has-an-intertwiner-torsor-obstruction: that isolates the abstract double-coset condition and leaves simultaneous packet factorization open; this constructs that factorization after a semantics-preserving half-edge gauge refinement.
  gauge-doubling-gives-selector-flip-symmetries: that gives one private share pair per context occurrence and a global flip action; this duplicates a share pair for each graph incidence so every reset has its own tensor factor.
  all-bcs-contexts-share-one-hyperoctahedral-signed-type: that gives one full-support predicate type; this adds a finite menu of subset-support types so an arbitrary exact HALT representation extends even when some allowed atoms have zero weight.
---

The exact HALT completeness condition `(FTC4)` can be closed.  The required
change is to make “incidence-private” literal: if the same context variable
is used on two different graph edges, give the two half-edges different
gauge share pairs.  Their products are still the same original logical word.
This refinement preserves the BCS algebra and the native mark, while making
the gauge Hilbert space a tensor product over graph edges.

The construction below concerns exact completeness only.  It does not prove
any finite-dimensional packet saturation or Gram estimate.

## A finite packet menu handles zero-weight allowed atoms

Let `R subset {+1,-1}^U` be the allowed set of one finite context.  Fix one
integer `D>=3` divisible by the cardinality of every nonempty subset of `R`.
For each nonempty `S subset R`, take a copy

```text
K_S=(C_2)^D semidirect S_D                                  (IPG1)
```

and label its natural signed-permutation coordinates by

```text
S times [D/|S|].                                            (IPG2)
```

For `x in U`, let `d_(S,x)` be the diagonal sign whose value at `(a,j)` is
`a_x`.  Put

```text
K_R=product_(empty != S subset R) K_S,
d_x=product_S d_(S,x),
J_R=product_S (-I_D)_S.                                    (IPG3)
```

For every nonempty `S`, the product group `K_R` has an irreducible type
`rho_S`: use the natural representation on the `S` factor and the trivial
representation on every other factor.  The joint spectrum of `(d_x)_x` in
`rho_S` is exactly `S`, every atom with the same positive multiplicity, and
`rho_S(J_R)=-I`.  Thus all menu types use one common marked sign and one
common dimension `D`.

Now let `(X_x)_x` be an exact commuting context representation whose set of
nonzero joint atoms is `S_pi subset R`.  After countable amplification, each
nonzero atom has Hilbert dimension `aleph_0`.  Therefore

```text
(X_x)_x tensor I_(ell2)
  is unitarily equivalent to
(rho_(S_pi)(d_x))_x tensor I_(ell2).                    (IPG4)
```

Pulling the remaining generators of `K_R` back through this unitary extends
the given context representation to the fixed finite packet `K_R`.

This removes a real exact-completeness gap in a single full-support
hyperoctahedral type.  Countable amplification cannot create a missing
allowed atom, but the finite menu `(IPG3)` already contains the type whose
support is precisely the set of atoms that actually occur.  The menu is
finite and computable from the context table; no HALT information enters the
presentation.

The same construction applies to a gauge-doubled context: replace `R` by its
finite lifted allowed set.  It remains a fixed finite menu.

## Half-edge gauge refinement

Let `Y` be the native Fanizza incidence graph.  For every oriented incidence
of a logical variable `X_x` on an edge `e={c,d}`, adjoin separate endpoint
shares

```text
A_(c,e,x), B_(c,e,x),     X_x=A_(c,e,x)B_(c,e,x),
A_(d,e,x), B_(d,e,x),     X_x=A_(d,e,x)B_(d,e,x).       (IPG5)
```

All shares belonging to one context commute.  Replacing a logical occurrence
inside a lifted predicate by either product in `(IPG5)` leaves the original
predicate unchanged.  Sending every `A` to `1` and every `B` to `X_x` is a
left inverse, so this refinement preserves every nonzero logical mark.

Start with any exact marked representation `pi` of the original Fanizza
system in the standard marked sector `pi(J)=-I`.  For an edge carrying `k_e`
shared logical bits, put

```text
K_e=(C^2)^(tensor k_e),
K_gauge=tensor_(e in E(Y)) K_e.                         (IPG6)
```

On the qubit belonging to `(e,x)`, represent the source endpoint shares by

```text
A_(c,e,x)=Z_(e,x),
B_(c,e,x)=pi(X_x) Z_(e,x),                              (IPG7)
```

and the target endpoint shares by

```text
A_(d,e,x)=X_(e,x),
B_(d,e,x)=pi(X_x) X_(e,x).                              (IPG8)
```

The Pauli operators act only on `K_e`; all logical operators act on the
original space.  Hence each pair in `(IPG7)--(IPG8)` consists of commuting
involutions and has product `pi(X_x)`.  At a fixed context, different
half-edge gauges live on different tensor factors, so all lifted context
variables commute exactly.

Let `W_e` be the tensor product of Hadamards on `K_e`.  It fixes every
logical word and sends the source gauge chart to the target chart:

```text
W_e Z_(e,x) W_e^*=X_(e,x).                              (IPG9)
```

This explicitly realizes the two-sided Pauli connector on an
incidence-private factor.  No orbit-covariantization argument is needed,
although the same representation is the Fourier form of the finite gauge
orbit.  In the finite presentation, impose the cross-edge Pauli commutators
and identify their central signs, so all edge factors form one extraspecial
group `E_M`.  The displayed tensor product is its unique `J=-1` spin type.
Add one common countable amplification.

For each context `c`, the joint support of its lifted commuting tuple is

```text
S_c^pi times {+1,-1}^(number of incident gauge bits),  (IPG10)
```

where `S_c^pi` is the nonzero logical context support of `pi`.  Every atom in
`(IPG10)` has infinite multiplicity.  Apply `(IPG1)--(IPG4)` to extend the
whole tuple to its fixed support-menu Schur packet.  The auxiliary packet
generators for distinct contexts are otherwise unrelated, so these
extensions can be made simultaneously on the same Hilbert space.  This is
the promised full Schur/Pauli packet factorization

```text
H=(H_pi tensor ell2)
   tensor K_DZ tensor K_ZR tensor K_DR tensor K_DX,     (IPG11)
```

with further leaf/private factors included as needed.  The native marked
word acts as `pi(mark) tensor I` and remains nontrivial.

## Explicit closure of the triangle torsors

Write `W_DZ,W_ZR,W_DR` for the private resets on the three triangle factors.
They commute because their tensor supports are disjoint.  The shared logical
separator words are already literally the same operators at their two
endpoints, so their logical edge implementers may all be chosen to be the
identity.  Define

```text
U_DZ=W_DZ W_DR,
U_ZR=W_ZR,
U_DR=W_ZR W_DZ W_DR.                                  (IPG12)
```

Then

```text
U_ZR U_DZ=U_DR.                                       (IPG13)
```

For the `D->Z` edge, `U_DZ` has the required reset `W_DZ`; its extra action
on `K_DR` is invisible because the `D->Z` edge group acts trivially there.
Likewise `U_ZR` has the required `W_ZR`.  For the direct `D->R` edge,
`U_DR` has the required action `W_DR`, while its actions on `K_DZ,K_ZR` are
invisible to that edge group.  Thus

```text
U_DZ in I_DZ(pi),
U_ZR in I_ZR(pi),
U_DR in I_DR(pi),
U_DR=U_ZR U_DZ.                                       (IPG14)
```

This proves the torsor intersection `(FTC4)`.  The `C_X` leaf uses its own
factor and imposes no cycle equation.

If an edge reset is block-controlled by its shared separator character, the
same proof applies.  The three native separator involutions
`O_Q,O_P,Z_tilde` commute pairwise, so the controlled `W_e` still commute.

## Why the refinement is necessary

With only one private gauge register for a context-variable used on two
different edges, the two required resets act on the same factor.  Their
product may differ from the direct-edge reset by a genuine unitary cocycle;
this is exactly the counterexample mechanism in
`fanizza-triangle-two-cell-has-an-intertwiner-torsor-obstruction`.
Countable amplification does not remove it.

The smallest exact obstruction was therefore not a property of the Fanizza
logical triangle.  It was reuse of a private gauge coordinate around a
cycle.  Half-edge duplication removes that reuse while fixing every logical
product, so it is semantically free.

## Scope

The literal triangular relation

```text
U_ZR U_DZ=U_DR                                         (IPG15)
```

now passes the exact HALT firewall for the full finite packet assembly.  This
closes `(FTC6a)--(FTC6c)` and the exact developability issue only.  It does
not prove that finite-dimensional approximate representations select the
same Gram state, accept the predicates on that state, or satisfy the anchor
rows `(FTC8)--(FTC10)`.

`half-edge-gauges-preserve-fanizza-gap` audits the finite-matrix cost of this
refinement.  Tying every duplicated share product to the same global logical
word makes coarsening over gauge signs an exact decoder back to the original
context PVM, so the static game gap is unchanged.  Putting all half-edge
Pauli pairs in one extraspecial central product gives canonical spin mass
`1/2`, independent of their number.  The only surviving finite problem is
the pre-existing task of putting the different selected context packets on
one positive Gram state.
