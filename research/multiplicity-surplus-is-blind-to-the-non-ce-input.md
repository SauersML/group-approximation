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

**(BLD4)**  Therefore the non-CE hypothesis is consumed nowhere except inside
the return transducer itself, and **any proof of Target 11.1 that does not
visibly use it is wrong**.  This is a checkable test, not a slogan: run the
candidate transducer argument on a classically unsatisfiable CSP and confirm
that it fails.

**The sharper form, and where it bites first.**  The class-two packet declares
its own selectors `z_l` **central**.  If context packets are glued over shared
selectors by an amalgam, a selector central in each factor is central in the
amalgam, so the BCS variables become globally commuting and the system
degenerates to exactly the classical CSP of `(BLD2)`.  Breaking that degeneracy
is not an implementation detail of the return transducer; it is the transducer.
Compare `supercritical-network-needs-noncanonical-cuts`, which is the same
phenomenon in the branching lane: the object that must fail in the exact model
is precisely the object the construction is trying to build.
