---
rg: 2
id: literal-group-factorization-property
kind: claim
title: The literal finitely presented group has Kirchberg's factorization property
distinct_from:
  literal-group-sofic: that is permutation approximation of E in normalized Hamming distance; this asks that the canonical trace of C*(E) be amenable in Brown's sense, which is soficity plus a u.c.p. lifting of the resulting tracial-ultraproduct representation, and the lifting is the whole content.
  literal-central-mark-corona-invisible: that is an operator-norm obstruction; this is a Hilbert--Schmidt-norm approximation property with a lifting clause, and the two are independent.
artifacts:
  - GroupApproximation/Manuscript/NinetyNineProblems/FactorizationProperty.lean
  - GroupApproximation/Manuscript/NinetyNineProblems/ProblemX.lean
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

The literal finitely presented group `E` of `non_mf_groups_exist.tex`
(`LiteralNonMFPresentation.MarkedGroup` in Lean) has Kirchberg's
factorization property: the representation `C*(E) ⊙ C*(E) → B(ℓ²E)` given by
the left and right regular representations is continuous for the minimal
tensor norm.

Equivalent forms (Brown, Theorem 4.1.9 and Theorem 3.1.6, N. P. Brown, *Invariant means and finite representation theory of C\*-algebras*, Mem. Amer. Math. Soc. 184 (2006), no. 865): the
canonical trace `τ_E` on `C*(E)` is an amenable trace; there are u.c.p. maps
`φₙ : C*(E) → M_{kₙ}`, asymptotically multiplicative in the normalized
Hilbert--Schmidt norm, with `tr ∘ φₙ → τ_E`.

## What is already in hand

`E` is sofic (`literal-group-sofic`, Lean
`LiteralSoficAssembly.markedGroup_isSofic`), so its canonical trace is a
*hyperlinear trace* in Shulman's sequential sense
(`ShulmanTrace.canonicalMaximalTrace_isHyperlinearTrace_of_isSofic`,
`GroupApproximation/Analysis/SoficHyperlinearBridge.lean`): bounded linear
`*`-preserving maps into matrices, asymptotically multiplicative in
Hilbert--Schmidt norm, recovering `τ_E`.  Equivalently `L(E)` embeds in
`R^ω`.  Amenability asks for those maps to be **completely positive**, i.e.
for the `*`-homomorphism `C*(E) → ∏M_{kₙ}/J_{HS}` to lift to a u.c.p. map
into `∏M_{kₙ}` (Brown, Theorem 3.1.7(2)).

## Why this is not automatic

Soficity does not give it: Thom (Groups Geom. Dyn. 4 (2010), arXiv:0810.2180)
constructs LEF, hence sofic, Kazhdan groups that are not residually finite, and
by Kirchberg's theorem (Math. Ann. 299 (1994): Kazhdan plus factorization
property implies residually finite) they lack the factorization property.  So
`hyperlinear-groups-have-factorization-property` is refuted and the generic
route is dead.  The lifting is automatic when `C*(E)` has Kirchberg's local
lifting property, which holds for free groups, amenable groups, limit groups,
3-manifold groups, certain one-relator groups and right-angled Artin groups
(Fournier-Facio--Willett, arXiv:2603.18456) but is not known for `E`
(`literal-group-local-lifting-property`, route `literal-fp-via-llp`).

Negative side: `E` is not itself Kazhdan (it is an HNN-type extension with a
free stable letter), so Kirchberg's obstruction does not apply directly; a
disproof would have to run the manuscript's compression-transport argument on
completely positive Hilbert--Schmidt-approximate models, which the manuscript
says it cannot do for merely bounded ones.

Open.  Any proof must use the structure of `E` (an HNN-type extension of a
Kazhdan--Clifford base with a telescope core that is locally residually
finite, `literal-telescope-core-lef`) rather than soficity alone.

Lean: `NinetyNineProblems.LiteralFactorizationProperty : Prop` (`GroupApproximation/Manuscript/NinetyNineProblems/ProblemX.lean`), defined
as `IsAmenableTrace` of the canonical trace of `C*(E)`; no inhabitant.

General form: `NinetyNineProblems.HasFactorizationProperty G` (`GroupApproximation/Manuscript/NinetyNineProblems/FactorizationProperty.lean`), with
`literalFactorizationProperty_iff` identifying the two.
