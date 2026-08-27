---
rg: 2
id: kazhdan-clifford-non-mf-construction
kind: claim
title: Kazhdan--Clifford construction of finitely presented non-MF groups
distinct_from:
  scaling-family-non-mf: This is the abstract construction from an arbitrary proper Kazhdan self-embedding; the scaling claim is its concrete affine family.
  torsion-free-finitely-presented-non-mf: This construction produces a nontrivial central involution; the other asks for a torsion-free example beyond the present mechanism.
  literal-group-not-sofic: This established claim is the operator-norm non-MF construction; the other asks whether one of its outputs, the literal group, additionally fails permutation approximation.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/KazhdanCliffordConstruction.lean
  - GroupApproximation/Sofic/LiteralNonMFEndpoint.lean
  - GroupApproximation/Endpoint/ChosenNonMFAudit.lean
---

Every finitely presented property-(T) group with a proper injective
self-embedding yields, from any element outside the image, a finitely
presented group with a nontrivial central involution killed by every
norm-matrix-corona representation.  In particular the constructed group is
not MF.

**LEAN STATUS.**  The reusable formal headline is
`KazhdanCliffordConstruction.kazhdanCliffordConstruction`.  The completely
instantiated finite presentation is closed by
`LiteralNonMFEndpoint.literal_not_isOperatorMF`; its marked sign is proved
nontrivial, central and involutive, and every genuine norm-matrix-corona
homomorphism is proved to kill it.  `Endpoint/ChosenNonMFAudit.lean` checks
both declarations' axiom closure.  This is a premise-free Lean endpoint, not
an informal invocation of a property-(T) or Clifford theorem from the
literature.
