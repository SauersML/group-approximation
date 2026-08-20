---
rg: 2
id: multiplicity-surplus-is-blind-to-the-non-ce-input
kind: claim
title: The forbidden-mass-to-multiplicity chain never consumes non-embeddability, so a transducer proof that ignores it is wrong
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  relator-only-hs-obstruction-has-trivial-model: that observes the identity tuple satisfies every relator, so an unmarked relator-only obstruction is impossible; this observes that a classically unsatisfiable CSP substitutes for the non-CE hypothesis everywhere downstream of the forbidden-mass bound.
  supercritical-network-needs-noncanonical-cuts: that is the branching-lane gate, saying a canonical network cannot be supercritical; this is the Schur-Clifford-lane gate, saying the multiplicity surplus does not know why the forbidden mass is positive.
  finite-graph-of-groups-representation-types-are-integer-flows: that is the representation-theoretic reason a graph of finite groups cannot supply the return; this is the logical reason no return construction can be correct unless it uses the non-CE hypothesis.
---

Let `B` be a finite Boolean constraint system and let `beta > 0` be a constant
such that every finite-dimensional contextwise-commuting involution tuple has
total forbidden mass at least `beta`.  Then:

**(BLD1)**  Everything downstream of that bound is insensitive to its origin.
`(9.2)` and `(9.3)` of the source note, and Target 11.1, refer to `beta` only as
a number.  Consequently, if a construction derives a positive normalized-HS
energy floor from `beta` together with the Schur--Clifford packets and a return
relation, the same derivation applies verbatim with `beta` replaced by any other
positive lower bound on forbidden mass.

**(BLD2)**  Such a bound exists without any non-embeddability input.  If `B` is
merely **classically unsatisfiable**, then for every tuple of *globally*
commuting involutions the joint spectral decomposition is a probability
distribution over assignments, and the expected number of violated contexts is
at least the classical unsatisfiability gap of `B`, which is positive.  No
ultraproduct, no MIP*, and no non-CE hypothesis is used.

**(BLD3)**  In that regime the conclusion is false.  The Schur--Clifford
compilation of a classically unsatisfiable `B`, assembled as a finite graph of
finite groups, has virtually free fundamental group and is therefore residually
finite, sofic and hyperlinear.  So the chain
`forbidden mass -> multiplicity surplus -> return -> energy floor`
**must** break for that instance.

**(BLD4)**  Therefore any purported return theorem whose only BCS-dependent
input is the number `beta` is blind to non-embeddability and cannot be correct.
A valid construction must consume the contextual operator structure of the
fixed BCS somewhere.  `non-ce-bcs-has-robust-approximate-energy-gap` does so by
applying compactness to one globally shared approximate tuple, including its
context commutator energy, rather than passing only the scalar `beta` into a
generic Bass--Serre return network.

**Correction to the naive centrality argument.**  Centrality does not
propagate transitively through a context hypergraph.  Amalgamating
`<x,y>` and `<y,z>` over the central involution `y` forces `[x,y]=[y,z]=1`
but not `[x,z]=1`; the amalgam is `C_2 x (C_2*C_2)`.  Thus shared central
selectors do not by themselves make all BCS variables globally commuting.
What kills the naive construction is instead `(BLD3)`: a finite graph of
finite packet groups remains virtually free and its representation-type flow
absorbs the local multiplicity surplus.  The contextual gluing is legitimate;
the fixed-scale return is the obstruction.
