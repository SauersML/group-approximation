---
rg: 2
id: multiplicity-return-via-contextual-holonomy
kind: route
title: Robust shared-word energy plus local packet holonomy yields the multiplicity-return transducer
target: multiplicity-return-transducer
requires:
  - predicate-rank-gate-doubles-restriction-multiplicity
  - non-ce-bcs-has-robust-approximate-energy-gap
  - finite-schur-clifford-packet-flexible-hs-exactification
  - predicate-rank-jump-forces-adjoint-reynolds-gap
  - fixed-scale-contextual-multiplicity-holonomy
  - scaled-kazhdan-transport
  - contractive-computation-ladder
  - bounded-overlap-syndrome-energy-accounting
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
---

The robust approximate BCS gap is applied directly to the original shared
selector word for each variable.  If context commutator relators do not already
pay constant energy, it leaves positive total forbidden-product mass.  Local
flexible exactification supplies genuine finite packet sectors, and
fixed-length telescoping transfers that mass without requiring the
context-dependent corrections to coincide.

On each forbidden sector the predicate rank gate doubles restriction
multiplicity.  Equivalently, the explicit Reynolds-gap lemma exposes a
positive-density projection in the adjoint space between the `A_f` and `B_f`
commutants.  Fixed-scale contextual holonomy transports this projection around
a recurrent cycle and compares it after return at the common baseline scale.
`scaled-kazhdan-transport` supplies the scale-free transport input;
alternatively the resulting positive-density contraction recursion is summed
by `contractive-computation-ladder`.  Bounded-overlap accounting charges the
extensive mismatch to total normalized-HS relator energy.  These are exactly
clauses 1--5 of `multiplicity-return-transducer`.
