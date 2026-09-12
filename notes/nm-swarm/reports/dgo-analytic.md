# Lane dgo-analytic (and helper H2 hull-assembly) — report

Non-MF verbatim formalization swarm, 2026-09-11.  Clone cs-limit.

## Scope 1: Dahmani–Guirardel–Osin Theorem 2.35, analytic half

`cor:regular-nonmf-algebra` cites DGO 2.35 for simplicity and uniqueness of the
trace of `C*_r(Q)`.  The route chosen with the lead (route B): Abbott–Dahmani's
property `P_naive` gives Powers' averaging estimate, and the estimate gives both
clauses.  No classical C⋆-algebra theorem is used (not Powers, Akemann–Lee, or
Breuillard–Kalantar–Kennedy–Ozawa).

Closed chain, all compiled (classical axioms only):

```
NaiveFreeProductProperty G                    Algebra/NaiveFreeProductProperty
  -> PingPongConjugateProperty G              Algebra/NaiveFreeProductPingPong
  -> ConjugateAveragingCriterion G            Analysis/PowersPingPongEstimate
  -> PowersAveragingEstimate G                Analysis/ConjugateAveragingCriterion
  -> simple C*_r(G) and unique tracial state  Analysis/PowersAveraging, PowersAveragingUniqueTrace
  -> DGOTheorem235Printed                     Manuscript/NonMF/DGO235FromNaiveFreeProduct
  -> SimpleUniqueTraceAtHypEmbedded           Manuscript/NonMF/SimpleUniqueTraceFromNaiveFreeProduct
```

Endpoints:

* `TorsionFreePrinted.dgoTheorem235Printed_of_naiveFreeProduct :
  NaiveFreeProductAtAcylindricallyHyperbolic → DGOTheorem235Printed`
* `TorsionFreePrinted.simpleUniqueTraceAtHypEmbedded_of_naiveFreeProduct :
  NaiveFreeProductAtAcylindricallyHyperbolic → SimpleUniqueTraceAtHypEmbedded`
  (through dgo-geometric's Osin `(AH₄) ⇒ (AH₁)`)

Residual: exactly one Prop, `NaiveFreeProductAtAcylindricallyHyperbolic`
(owner dgo-geometric).

Also compiled: the rescued 09-09 reductions (`DGO235UniqueTraceFromAveraging`,
`DGO235FromPowersProperty`, `DGO235PowersRoute`, `DGO235PrintedFromGeometry`,
`PowersAveragingFromPartition`, `PowersAveragingFromPowersProperty`,
`PowersAveragingSingleClass`, `PowersAveragingComposition`,
`GroupHilbertSubsetProjection`) and the corrected `DGOTheorem235Slice` header.

Landings: 100539f34, 460831be0, 04cc4aa44, 2a711b6bd, d748a8d40, 14914dfd2,
47c5d4b44, 0cdf0b924.  Census row: `metadata/nm-census-rows/dgo-analytic.tsv`
(`LINE:1688 partial`, pending the P_naive producer).

## Scope 2 (helper H2 hull-assembly): Osin Appendix §9 assembly

* `GGT/VanKampen/Estimating/OsinAppendixAssembly.lean` (ce6930740):
  `OsinSection97InputsStatement`, `osinLemma97Section_of_inputs`,
  `relativeGreendlingerQuasiGeodesicLeastArea_of_inputs`, and the two
  ρ-thresholds `exists_rho_widthBudget`, `exists_rho_muSqrt`.
* `GGT/VanKampen/Estimating/OsinAppendixAssemblyPocket.lean` (a956f3d3d): the
  descent of Lemma 9.7(b): `RealizedSectionFamily.ExteriorLarge`,
  `ExteriorUniqueAt`, `exteriorSectionLength`, the named input
  `OsinExteriorDoubleCut`, the pocket estimate
  `OsinExteriorDoubleCut.lastSection_total_gt`, and the induction on `m(Π)`
  `exists_of_exteriorDescent`.

### Two findings on Osin's proof of Lemma 9.7(b) (arXiv:math/0411039v3, pp. 34–35)

1. **Threshold slip** (correction approved): `Π` minimises `m(Π)` among cells
   above `1 − 11μ`, but the new cell `Π′` is only shown above `1 − 13μ`, so it need
   not lie in the class.  The class is taken at `1 − 13μ` (nonempty from
   Corollary 9.6's `11μ` cell).
2. **The step needs clause (a) at the pocket.**  Osin's (40) at `1 − 11μ` is
   "Corollary 9.6 and the inductive assumption" at the pocket `Γ_1`, i.e. clause
   (a) `(∗)` plus Lemma 9.4 at a smaller diagram.  `OsinLemma97Below`, the
   inductive hypothesis `DescentInput` receives, carries only clause (b), whose
   `1 − 13μ` at the pocket gives only `1 − 15μ` towards `t_2`.  So the step
   producer must either receive clause (a) of the smaller diagrams (the induction
   in `OsinAppendixSectionInduction` already proves `(a) ∧ (b)`) or carry the
   `11μ` cell of the pocket as an input.

Open: `OsinAppendixAssemblyDescent.lean` (named merge/step producers,
`descentInput_of_exteriorDescent`), waiting on hull-select's clause (b) batch.

## Fleet traps found here

* `autoImplicit` is on: a missing import reads "Function expected … unknown
  identifier treated as implicitly bound".
* `push_neg` and `ContinuousLinearMap.add_apply` are deprecated at the pin.
* `set 𝔅 := <operator type>` shadowed an argument and broke rewrites.
* `congr 1` can close the goal, leaving the next tactic with "no goals".
* `positivity` on a `set` of a `Finset.card` timed out in `whnf`.
* `rw [a.2.source = i]` through `a.2.sourceArc.length / (cell Delta a.2.source)…`
  fails ("motive is not type correct"); rewrite a separate `have` about the cell
  length.
* `Monoid.CoprodI.of m` over `fun b ↦ ↥(S b)` infers the family as `Subtype`
  over `G → Prop`; state letters over an `abbrev` family.
