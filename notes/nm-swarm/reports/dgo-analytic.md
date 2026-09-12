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

* `GGT/VanKampen/Estimating/OsinAppendixAssemblyDescent.lean` (57ddccb86, dea18154c,
  5f5dddd41; compiled in probe 0912-001046-51202): design F2 (approved).
  `OsinDescentMergeInput` and `OsinDescentStepInput` (named producers quoting
  Osin; the step carries Corollary 9.6 at the pocket), `exists_exteriorUniqueAt_of_merge_step`,
  `exists_sectionSelection_of_exteriorUniqueAt`, `osinLemma97bConclusion_of_exteriorUniqueAt`
  (clause (b) in hull-select's shape, disjointness from compatibility, distinct
  regions from nondegenerate target arcs), and
  `descentInput_of_merge_step : OsinDescentMergeInput → OsinDescentStepInput → … → DescentInput`.
* Repair 948130d79: the wired pocket module after eb4bc56f4 changed the
  signature of `contiguityDegree_lt_mu_of_o52` (the root was red until then).

Residual of G6 on route F2: the two named producers, `OsinDescentMergeInput`
(merge through `R`-cell-free pockets) and `OsinDescentStepInput` (pocket,
Corollary 9.6 at the pocket, uniqueness to `s_1, t_1, s_2`, glue-back with
smaller measure).

### Finding 3: route F2's step producer is circular; replaced by the pocket cut

`OsinDescentStepInput` carries the `11μ` cell of Corollary 9.6 at the pocket.
Producing it needs clause (a) of Lemma 9.7 at the smaller diagram, and
`OsinLemma97Below` does not carry clause (a).  So any producer of the step would
have to run Lemma 9.7 itself.  The approved replacement (lead, 09-12) keeps
`OsinAppendixAssemblyDescent` unchanged.  It runs Corollary 9.6 at each pocket
directly from `OsinLemma97Below` and a fresh globally distinguished section
system of the pocket, with strong induction on the pocket's `R`-cell count.  No
extremality transport is needed.  The only leaf is the planar cut.

* `GGT/VanKampen/Estimating/OsinAppendixDescentCut.lean` (4f3d38859, 08381ed21):
  the leaf `OsinSectionPocketCut` (extends `OsinExteriorDoubleCut` with
  `sectionTransport` to section `j` of `Δ` at part 3),
  `SectionPocketCutInput`, `OsinLemma97Below.mono`,
  `OsinSectionPocketCut.false_of_inner`, `RealizedSectionFamily.emptyOfLeastArea`,
  `osinLemma97bConclusion_of_region`.
* `GGT/VanKampen/Estimating/OsinAppendixDescentInduction.lean` (f82dfe0c3,
  08381ed21): `exists_elevenCell_of_below` (Corollary 9.6 at a least-area diagram
  below the induction measure), `OsinSectionPocketCut.exists_large_region` (the
  pocket induction, conclusion `1 − 13μ` towards section `j`), and
  `descentInput_of_sectionPocketCut : … → SectionPocketCutInput → DescentInput`.
  Both modules compiled in probe 0912-100628-69222 (base 08381ed21), classical
  axioms only.
* `GGT/VanKampen/Estimating/OsinAppendixLemma97Pocket.lean` (4b9f8144d; compiled
  in probe 0912-101449-41267, base 4b9f8144d, classical axioms only):
  `OsinSection97PocketInputsStatement` (cut producers, Euler count,
  `SectionPocketCutInput`), `osinSection97Inputs_of_pocketInputs`,
  `osinLemma97Section_of_pocketInputs` and
  `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputs`, with O52 given by
  `Embedded.o52LeastArea`.

Residual of G6 on this route: `SectionPocketCutInput` only.  hull-respell
produces it (Estimating/OsinAppendixPocketCutProducer; the empty-side pinch
case goes through PinchSplit).  The transport fields `cellTransport` and
`sectionTransport` are the two targets of go-lemma42's
`DiscDiagram.regionPiece_transport` on hull-select's `DiscDiagram.regionPiece`.

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
* `simpa … using h` compares the final types at reducible transparency, so it
  fails when an implicit argument is a def projection (`(emptyOfLeastArea …).diagram`
  against `Y`); use `rw` then `exact`.
* `nmprobe.sh` refuses when a file listed in the lane's `.files` is missing
  locally; write the file before listing it.
