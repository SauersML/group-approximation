---
rg: 2
id: tensor-context-types-classicalize-common-source
kind: claim
title: Tensorized selected context types classicalize their common source
distinct_from:
  role-hyperoctahedral-type-has-an-orthogonal-amalgam-model: that keeps context packets free over one D8 and rotates their selected carriers apart; this forces a positive intersection by a full finite direct product and proves that the resulting carrier is semantically classical.
  finite-product-selected-type-mark-does-not-align-carriers: that shows products of noncommuting selected projections need not have a common meet; this assumes genuine tensor-factor projections, so the meet exists, and identifies the exact completeness obstruction which replaces alignment.
  finite-role-packet-cannot-supply-hybrid-predicate-row: that rules out one universally scalar nonlinear row in a finite marked packet; this allows the selected SMC row locally and proves that tensorizing all selected rows forces a global classical assignment.
  unconditional-bcs-ultraproduct-decoder-forces-ce: that rules out a decoder functorial on every tracial representation by a Connes-embedding consequence; this is a finite algebraic joint-spectrum obstruction on one tensorized carrier.
---

Let `B` be a finite Boolean constraint system with variable set `X`, context
set `C`, and no globally satisfying Boolean assignment.  Suppose that on a
projection `Q` each context `c` is represented by commuting involutions

```text
A_(c,x)                         (x in c),              (TCC1)
```

and that observables belonging to different contexts commute because the
selected context packets act on different tensor factors.  Suppose further
that shared-variable rows identify repeated occurrences on `Q`,

```text
A_(c,x)Q=B_xQ                    (x in c),             (TCC2)
```

and that the selected SMC predicate row kills every forbidden projector,

```text
F_c(A_(c,*))Q=0                  (c in C).             (TCC3)
```

Then

```text
Q=0.                                                     (TCC4)
```

The conclusion is representation-independent: it holds on an arbitrary
Hilbert space, not only in matrices or in a tracial representation.

Consequently the tempting promotion

```text
full direct product of selected context packets
 -> product selected projection Q
 -> private compressed D8 swaps S_c=j_cQ
 -> shared literal variables plus selected SMC rows                  (TCC5)
```

cannot preserve exact completeness for a perfect nonclassical gap BCS.  The
direct product does give a common positive canonical source, by
`private-d8-cube-has-one-common-source`, but it makes all pulled-back context
labels jointly compatible.  Exact consistency and predicate rows then turn
that source into a global classical assignment, which does not exist.

There is a sharp dichotomy.

- Tensor only the private D8 role cells.  Their bottom cube vertex is a
  common source, but the separately selected hyperoctahedral/SMC carriers
  can still be rotated apart inside its multiplicity space.
- Tensor the complete selected context packets.  Their product carrier has
  fixed positive regular mass, but `(TCC1)--(TCC3)` force it to vanish in
  every exact model of an unsatisfiable BCS.

Thus tensorized private packets do not close the selected-carrier promotion
axiom.  A successful construction must align context rows on one source
without making their local assignment algebras mutually commuting.  This is
exactly the non-functorial, matrix-only coupling sought by the common-swap
route.

This cannot be repaired by claiming that the direct-product packet embeds
for soundness while a different exact representation simply avoids `Q` for
completeness.  If the exact group relators imply `(TCC1)--(TCC3)` on the
group-algebra projection `Q`, then `(TCC4)` holds in the left regular
representation of the presented group.  But `Q` is nonzero in the group
algebra of the finite direct product by `(PDC5)`.  Hence the finite direct
product cannot inject into the presented group, and its canonical regular
trace no longer supplies the advertised positive source mass.  The same
relations cannot simultaneously provide packet embedding and annihilate
the product type.

There is also a fixed quantitative version.  Choose one occurrence
`c(x)` for every variable and put

```text
C_x=A_(c(x),x)Q.                                      (TCC6)
```

The `C_x` commute pairwise.  If `F_c(C_*)` denotes the forbidden projection
of context `c`, unsatisfiability gives the operator inequality

```text
sum_c F_c(C_*) >= Q.                                  (TCC7)
```

For a context of arity `k_c`, writing its forbidden projection as a sum of
Boolean atoms and telescoping products of contractions gives

```text
||F_c(C_*)-F_c(A_(c,*))||_2
 <= (|Bad_c|/2) sum_(x in c)||C_x-A_(c,x)Q||_2.       (TCC8)
```

Taking trace in `(TCC7)` and using `(TCC8)` shows that fixed positive source
mass must pay a dimension-free predicate/consistency error floor.  This is
soundness obtained at the price of killing the exact infinite witness, not a
non-hyperlinearity proof.
