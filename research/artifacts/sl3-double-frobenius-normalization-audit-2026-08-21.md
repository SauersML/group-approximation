# Frobenius and bounded-generation audit for the canonical SL3 arithmetic double

Date: 2026-08-21

Let

```text
C=SL_3(Z),   A=SL_3(Z[1/2]),   D=A *_C A.
```

This audit asks whether the simultaneous-two-vertex-outlier sector can be
removed by 2-Kazhdan/Frobenius stability or bounded generation.

## Exact normalization

For a `d x d` matrix,

```text
||X||_F = sqrt(d) ||X||_(2,d).
```

Known Frobenius-stability results use the unnormalized Frobenius norm: their
input is a defect tending to zero in `||.||_F`.  A normalized-HS microstate
only gives `delta_d->0` in `||.||_(2,d)`, i.e. Frobenius defect
`sqrt(d) delta_d`, with no rate relation between `d` and `delta_d`.

Canonical character does not add such a relation.  Replacing every matrix by
`m` identical diagonal blocks preserves every normalized word trace and every
normalized-HS word defect exactly, while multiplying every unnormalized
Frobenius defect by `sqrt(m)`.  The Cairn theorem
`sl3-canonical-double-replication-escapes-every-frobenius-basin` makes this
specific to the full canonical double: exact folding guarantees that a
sufficiently canonical assignment has some positive relator defect, which
can then be replicated above any prescribed Frobenius threshold.

Therefore no argument may infer

```text
canonical double microstate + normalized defect -> 0
    => unnormalized Frobenius defect -> 0.
```

This remains false even when all word traces, not merely a finite trace test,
converge to the canonical character.

## What a 2-Kazhdan theorem would actually need to provide

A GLOBAL dimension-independent homogeneous inequality such as

```text
dist_F(sigma, Rep_d(A)) <= C defect_F(sigma)              (H1)
```

would immediately normalize: divide `(H1)` by `sqrt(d)`.  Such an estimate
would be replica-invariant and would correct a vertex in normalized HS.
But qualitative Frobenius stability only applies inside the regime
`defect_F->0`; it does not assert `(H1)` for assignments whose Frobenius
defect grows.  The usual cohomological/Newton proof also needs entry into a
dimension-independent local basin.  Replication shows that canonical trace
cannot supply that entry.

The existing Bader--Sauer input recorded in Cairn gives degree-two vanishing
for higher matrix rank in the unnormalized/cohomological program, while the
rank-three case is not imported as a 2-Kazhdan theorem.  Even granting an
unnormalized Frobenius-stability theorem for `A` would not cross the
normalization firewall above.  What would cross it is the stronger global
homogeneous estimate `(H1)` or the operator-bounded primitive requested by
`bounded-degree-two-primitives-for-higher-rank-lattices`.

## Why bounded generation alone does not cross the firewall

Even granting bounded elementary generation of `A`, it begins only after
coherent approximate root-subgroup maps have been corrected.  It then
propagates their error through a bounded product.  It neither constructs
those corrected maps nor aligns their overlaps and Steinberg relations.

At the metric level, bounded word telescoping is homogeneous and
replica-invariant; it preserves the distinction between `||.||_F` and
`||.||_2` rather than eliminating it.  To make bounded generation useful one
still needs a dimension-free normalized-HS correction theorem for the root
packets and their compatibility.  Packaging that missing correction as
`(H1)` simply restates the stability gate.

## Minimal remaining positive target

The exact sufficient statement is now
`sl3-canonical-double-has-a-correctable-vertex`: every canonical double
microstate has at least one full `A` vertex close in normalized HS to a
genuine representation.  The established one-vertex anchor then corrects
the other vertex automatically.  Replication proves that this target cannot
be obtained by feeding canonical trace into an unnormalized Frobenius basin;
it must be proved natively in normalized HS or by a replica-homogeneous
global estimate.

