# cite-osin: the two sentences that cite Osin, *Acylindrically hyperbolic groups*

Snapshot: origin/main efd80066b (2026-09-12). The manuscript cites Osin twice, at tex 1659–1662 and 1725–1728. There are no other `\cite[...]{Osin}` sentences.

| tex | sentence | status | closed decl (named Prop) | citation decl | landed | green |
|---|---|---|---|---|---|---|
| 1659–1662 (`lem:saturation`, proof) | "The subgroup N is normal, and it is infinite because G is torsion-free and N≠1, so it acts non-elementarily on Cay(G,A) by Osin [Lemma 7.1]; since G is torsion-free, N normalizes no nontrivial finite subgroup, so N is suitable." | CLOSED | `OsinCitedSentences.manuscriptSentence_saturationSuitableClosed : SaturationSuitableSentence` | `GGT.OsinPrinted.osinLemma71Printed : OsinLemma71Printed`, `GGT.OsinPrinted.manuscriptSentence_saturationOsinClosed : SaturationOsinSentence` | efd80066b (new carrier); citation decls already on main | GREEN 0912-104514-46330 (base ef7d9c4dd; BUILT, #audit_closed_axioms passed) |
| 1725–1728 (`cor:regular-nonmf-algebra`, proof) | "The group Q is countable, torsion-free, and acylindrically hyperbolic, so it contains a non-degenerate hyperbolically embedded subgroup [Osin, Theorem 1.2] and has no nontrivial finite normal subgroup." | CLOSED | `OsinCitedSentences.manuscriptSentence_algebraOsinClosed : AlgebraOsinSentence` (Hull's Cayley-graph notion); `OsinCitedSentences.manuscriptSentence_algebraOsinClosedOsin : AlgebraOsinSentenceOsin` (Osin's notion) | `TorsionFreePrinted.exists_isNonDegenerate_isHypEmbedded`, `TorsionFreePrinted.osinTheorem12Printed_unconditional : OsinTheorem12Printed` | efd80066b (new carriers); citation decls already on main | GREEN 0912-104514-46330 (base ef7d9c4dd; BUILT, #audit_closed_axioms passed) |

## Route to the endpoints

All pieces are PROVED. None takes a literature binder.

**Osin, Lemma 7.1** (`GGT/OsinLemma71Printed.lean`)
- `osinLemma71Printed` has `#audit_closed_axioms`. It is proved from `Elementary.osinNonElementary_of_torsionFree_normal_closed` (`GGT/ElementaryOsinNormalClosed.lean`) and `TorsionFree.isSNormal_of_torsionFree` (`Manuscript/NonMF/Saturation.lean`).
- It reaches the root closure through `GGT.OsinLemma71PrintedReduction` and then `GGT.OsinLemma71PrintedReductionClosedCitations`, which `GroupApproximation.lean` imports.
- The remaining clauses come from `TorsionFreePrintedSentences.manuscriptSentence_saturationSuitable`. It is root-imported and uses torsion-freeness only.

**Osin, Theorem 1.2, `(AH₁) ⇒ (AH₄)`** (`Manuscript/NonMF/OsinTheorem12NonDegenerate.lean`, root-imported)
- `exists_isNonDegenerate_isHypEmbedded` has `#audit_axioms`. It is proved from:
  - `GGT.exists_ah3Data_of_isAcylindricallyHyperbolic`
  - `HullSC.not_isVirtuallyCyclic_of_actsNonElementarily`
  - `GGT.Elementary.dgoTheorem68_of_projection_unconditional` together with `dgoTheorem442_unconditional`
- The last clause comes from `TorsionFreePrintedSentences.manuscriptSentence_algebraTrivialFiniteRadical`.
- For Osin's notion, `GGT.isAcylindricallyHyperbolic_of_osin` (`GGT/AcylindricallyHyperbolicOsin.lean`) is proved from `Elementary.osinTheorem12_unconditional` `(AH₃) ⇒ (AH₁)` and `isWPDAt_of_isAcylindrical`. It reaches the root closure through `TorsionFreeOsinNotion` and `AcylindricallyHyperbolicLimitSetEasy`.

## New module

`GroupApproximation/Manuscript/NonMF/OsinCitedSentencesClosed.lean` is an orphan module. It states each whole printed sentence as one named `Prop` with a hypothesis-free proof and `#audit_closed_axioms`, so each census row can name a single closed endpoint. Before this, each row named one carrier per clause.

## Related, not owned here

- tex 1629, row a9dd4b90e479: the limit-set notion of acylindrical hyperbolicity (the hard direction of Osin's Theorem 1.1). That sentence cites Hull, Theorem 3.12, not Osin. OWNED BY sec5, dgo-geometric and cite-hull.
- Row f2bf6328169e, tex 1725: the DGO/GO sentence (DGO Theorem 2.35, GO Theorem 1.1). census2 U3 lists it as a stale re-grade for census-merge.

## Stale docstrings, reported to main; these files are not on any lane's list

- `Manuscript/NonMF/TorsionFreePrintedSentences.lean`: the docstring of `manuscriptSentence_algebraTrivialFiniteRadical` says "This development has no vocabulary for *hyperbolically embedded* … Osin's Theorem 1.2 is folded into that citation". Both claims are false on main: `GGT.IsHypEmbedded` and `exists_isNonDegenerate_isHypEmbedded` exist.
- `Manuscript/NonMF/TorsionFreePrintedSentences.lean`: the module header says the Osin 7.1 sentence "takes `OsinLemma71Printed`" as a binder, but the closed form `GGT.OsinPrinted.manuscriptSentence_saturationOsinClosed` exists.
- `GGT/OsinLemma71Printed.lean`, section "What is left for the lead": "`GroupApproximation.lean` still has to import this module". The module is now in the root closure, through `OsinLemma71PrintedReductionClosedCitations`.
