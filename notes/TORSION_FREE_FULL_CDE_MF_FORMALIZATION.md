# Torsion-free full CDE-MF-radical formalization

This document is the certification boundary for the proposed
Fournier--Facio--Hull construction.  The relevant Lean files are:

- `GroupApproximation/Sofic/CDEMFRadical.lean`;
- `GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean`;
- `GroupApproximation/Sofic/TorsionFreeFullMFConsequences.lean`;
- `GroupApproximation/Analysis/TorsionFreeFullMFCStarConsequences.lean`.

Throughout, **MF group** means the Carrión--Dadarlat--Eckhardt property:
embedding of a countable group in the unitary group of a genuine cofinite
norm-matrix C-star corona.  The public predicate is `IsCDEOperatorMF`; its
proved equivalent coordinate presentation is `IsOperatorMF`.  The subgroup
`cdeMFResidual G` is the intersection of the kernels of all literal CDE
corona representations.

## What is proved without external assumptions

For any `FournierFacioDefectData P E`, Lean proves:

- `core_transported`: the transported root is the selected simple-factor
  element `s`;
- `core_defectNormal_eq`: the compression defect is exactly the normal
  closure of the commutators `[s,ι(p)]`;
- `simpleSubgroup_le_defectNormal`: simplicity and one nontrivial commutator
  saturate the entire simple subgroup into the defect.

For any `RelativeCommonQuotientData D B` and a proof that `B` has property
`(T)`, `toDefectRoutingData` derives property `(T)` of the common quotient
from the supplied epimorphism.  It does not postulate property `(T)` of that
quotient separately.

For any `DefectRoutingData D`, Lean proves:

- finite presentation, two-generation, power torsion-freeness, property
  `(T)`, and nontriviality of the routed quotient;
- `mapped_defectNormal_eq_top`;
- `cdeMFResidual_eq_top`, `coronaMFResidual_eq_top`, and
  `normMFResidual_eq_top`;
- triviality of every literal CDE-corona representation and of every
  homomorphism to an operator-MF group;
- failure of both `IsCDEOperatorMF` and its equivalent coordinate predicate;
- inheritance of full radical by every quotient and non-MF-ness of every
  nontrivial quotient.

The consequence file proves, from explicit proof-carrying construction data:

- nonsoficity via `NonsoficCriterionData`;
- the rank-two free-group quotient package;
- the simple, torsion-free, two-conjugacy-class quotient package;
- full-radical simple envelopes;
- SQ-universal containers;
- the universal finitely presented torsion-free Kazhdan-group consequences.

The C-star consequence file proves that the concrete reduced group C-star
algebra is not an MF C-star algebra and that all of its nonempty finite matrix
amplifications are finite.  Claims of simplicity, unique trace, and stable
rank one are not represented because their acylindrically-hyperbolic inputs
are absent from the library.

## Exact unformalized existence boundary

There is deliberately **no** theorem of the form

```lean
∃ Q, IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧
  IsPowerTorsionFree Q ∧ HasKazhdanPropertyT Q ∧
  cdeMFResidual Q = ⊤ ∧ ¬ IsSofic Q
```

without an input structure.  Producing the required structures still uses
group theory not available in Mathlib or this repository:

1. the particular universal/finitely presented torsion-free input groups and
   embeddings used by Fournier--Facio;
2. the suitable-subgroup extraction inside the normal closure of the simple
   factor;
3. Hull's two-stage relative common-quotient construction, including
   protected-set injectivity, finite presentation, torsion preservation,
   two-generation, and routing of the prescribed defect onto the quotient;
4. the acylindrical-hyperbolicity conclusions;
5. the external two-conjugacy-class, SQ-universal, and relative simple-envelope
   existence theorems;
6. Raum's stable-rank-one theorem and the external reduced-C-star
   simplicity/unique-trace theorem.

These results are represented only by structures whose fields are consumed
by checked Lean proofs.  They are not declared as axioms, selected by
`Classical.choice`, or hidden in typeclass instances.  Consequently the
development certifies the algebraic and CDE-MF implications of the proposed
construction, but not the unconditional existence of its small-cancellation
input data.

## Relation to the literal eight-generator manuscript group

The distinct literal `E` gap in `non_mf_groups_exist.tex` is now closed.
`LiteralP13HodgeCertificate` proves the exact rational property-`(T)` input,
`LiteralBaseP13PropertyTBridge` transports it to the raw six-generator base,
and `LiteralNonMFEndpoint.manuscriptTheoremA` gives the literal MF endpoint
without a caller premise.
