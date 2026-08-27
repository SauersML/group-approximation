---
rg: 2
id: literal-group-factorization-property
kind: claim
title: The literal finitely presented group has Kirchberg's factorization property
distinct_from:
  literal-group-sofic: that is permutation approximation of E in normalized Hamming distance; this asks that the canonical trace of C*(E) be amenable in Brown's sense, which is soficity plus a u.c.p. lifting of the resulting tracial-ultraproduct representation, and the lifting is the whole content.
  literal-central-mark-corona-invisible: that is an operator-norm obstruction; this is a Hilbert--Schmidt-norm approximation property with a lifting clause, and the two are independent.
artifacts:
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

"Hyperlinear implies factorization property" is not a theorem.  By
Kirchberg (Math. Ann. 299 (1994)) a Kazhdan group with the factorization
property is residually finite, so that implication would make every
hyperlinear Kazhdan group residually finite, and in particular would prove the
manuscript's simple Kazhdan group `H` non-hyperlinear --- a non-hyperlinear
group, which nobody has.  The lifting is automatic when `C*(E)` has
Kirchberg's lifting property, which it does for free groups and which is
not known for `E`.  This is `hyperlinear-groups-have-factorization-property`.

Open.  Any proof must use the structure of `E` (an HNN-type extension of a
Kazhdan--Clifford base with a telescope core that is locally residually
finite, `literal-telescope-core-lef`) rather than soficity alone.
