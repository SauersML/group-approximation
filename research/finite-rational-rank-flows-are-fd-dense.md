---
rg: 2
id: finite-rational-rank-flows-are-fd-dense
kind: claim
title: Every finite rational tracial rank flow is approximable by finite-dimensional stationary flows
distinct_from:
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that constructs one strictly positive regular flow for every finite graph of finite groups; this approximates an arbitrary prescribed real tracial flow and preserves its marked masses.
  finite-graph-of-groups-representation-types-are-integer-flows: that identifies exact integer points for a graph of finite groups; this isolates the general rational-polyhedral density argument and its precise boundary at multiplicity holonomy.
  atlas-a4-context-types-live-in-fixed-rational-polytope: that applies the integer-flow cone to one fixed Atlas network; this applies to every finite rational rank-flow diagram.
  tracial-bcs-has-rational-balanced-hyperoctahedral-atlas: that rationalizes one BCS marginal polytope; this gives the abstract representation-ring statement and explains why rank rationalization never resolves cycle holonomy.
---

**ESTABLISHED.**  Fix finitely many finite-dimensional semisimple complex
`*`-algebra packets.  Choose bases of simple representation types, and suppose
all compatibility/return data retained by a proposed compiler consist only of

```text
nonnegative type multiplicities,
integer restriction/induction matrices,
rational linear equalities and inequalities among their ranks,
and common total-dimension normalizations.                         (RFD1)
```

Let `P` be the resulting normalized stationary-flow set.  If an exact finite
tracial completion supplies a flow `x in P`, then for every `epsilon>0` there
is a rational flow `y in P` with

```text
||x-y||_infinity<epsilon,                                         (RFD2)
```

lying in the same minimal face as `x`.  In particular every coordinate which
vanishes at `x` still vanishes at `y`, while every fixed strictly positive
marked mass remains positive for sufficiently small `epsilon`.

After clearing one common denominator, `y` is an integral multiplicity flow
and is realized by finite-dimensional packet representations with exactly
matching edge/restriction ranks.  Thus no positive normalized-HS obstruction
can depend only on a finite rational representation-ring/rank flow: every
tracial zero of that data is a limit of finite-dimensional stationary zeros.

## Precise missing hypothesis

The conclusion stops when a return cell constrains the **chosen multiplicity
intertwiners**, rather than only their source and target ranks.  A cycle word,
projective cocycle, or polynomial relation among multiplicity unitaries is not
a coordinate of `P`.  To approximate that extra datum one needs an additional
hypothesis, such as:

```text
the holonomy algebra is finite dimensional;
the particular holonomy trace is Connes embeddable;
or a quantitative stability theorem corrects its matrix microstates.       (RFD3)
```

Without `(RFD3)`, rationalizing ranks says nothing about simultaneous
finite-dimensional realization of the holonomy.  This is exactly why the
regular stationary-flow theorem leaves two-cells and cycle holonomy as the
only possible finite-packet obstruction.

