# cite-sofic: Elek–Szabó, Kun, Kun–Thom citation sentences

Lane scope:
- ElekSzabo Theorem 1 (tex 262 and 1568).
- Kun16 + KT19 (tex 328).
- Abstract row a16637da7249.
- Root-wave modules AmenableTraceSentencesB and BinaryExampleSentences.

Module: `GroupApproximation/Manuscript/NonMFSentences/SoficCitationSentences.lean` (new orphan; the lane's only .files entry).
- Landed at 3d2a4eac16c7667e09e9816cbb1a854b06d895fe.
- PROBE GREEN, tag 0912-104415-40292; the landed file's md5 c0a28e7e58eeba01fdc9d25d626b4dac equals the green evidence.
- The audit block covers every endpoint: `#audit_closed_axioms` on the three printed theorems and `#audit_axioms` on the two lemmas. The guard throws on any axiom outside propext, Classical.choice and Quot.sound.
- Needs wiring by the lead; this lane does not wire.

## Per sentence

| row | tex | sentence | status | carrier |
|---|---|---|---|---|
| f969236a73d8 | 262 | "The group W is sofic because locally residually finite groups are sofic and soficity passes to extensions with amenable quotient [ES, Thm 1]." | CLOSED (3d2a4eac1, green 0912-104415-40292) | `GroupApproximation.SoficCitationSentences.printedIntroWSoficMechanism : PrintedIntroWSoficMechanism`. Five conjuncts: locally RF groups are sofic; Elek–Szabó at printed generality; W₀ is locally RF; W ≅ W₀ ⋊ ℤ; W is sofic. The old row decl `manuscriptWSoficFromLocallyRFExtension` is only the ℤ-semidirect instance with an `IsLocallyResiduallyFinite` hypothesis. |
| 2c614717a212 | 1566–1568 | "The group W₀ is their directed union, and W/W₀ ≅ ℤ is amenable. Soficity passes to directed unions and to extensions with amenable quotient [ES, Thm 1], so W is sofic." | CLOSED (3d2a4eac1, green 0912-104415-40292) | `GroupApproximation.SoficCitationSentences.printedCliffordWDirectedUnionSofic : PrintedCliffordWDirectedUnionSofic`. Six conjuncts: finite subsets of W₀ lie in f.g. sofic subgroups; W ≅ W₀ ⋊ ℤ with W₀ = ker(W₀ ⋊ ℤ → ℤ), a surjection; ℤ is amenable; directed-union permanence at printed generality; Elek–Szabó at printed generality; W is sofic for every RF Γ with a finite-index injective α. The row's existing decls stay valid; `AmenableTraceTheorem.manuscriptSentence_wSoficMechanism` is a correct FQN, because `Sofic/CliffordWitnessSoficSentences.lean` opens `namespace AmenableTraceTheorem`. |
| de554b7cd342 | 328 | "There, soficity and the rigidity theorems of Kun [Ku16] and Kun–Thom [KT19] force the centralizing subgroup to be locally embeddable into finite groups, and a copy of Thompson's group V gives the contradiction." | IN PROGRESS: carrier landed and green; grading under review. The row was `attribution`; cite-kazhdan confirmed this row is mine. | `GroupApproximation.SoficCitationSentences.printedKunThomRigidityContradiction : PrintedKunThomRigidityContradiction`. Conjuncts: (1) for every `CompressionSetup G Γ J` with property (T) for G and Γ, `IsSofic G → IsLEF J` (`isLEF_of_isSofic`, from the Kun fixed decomposition); (2) `¬ IsLEF V` (`BinaryLeavitt.thompsonV_not_isLEF`); (3) a copy of V in J contradicts soficity. The carrier assumes (T) for the ambient group as well as for Γ. Checking that against the printed configuration, where only L is said to have (T), before choosing a grade (rule 9: an extra hypothesis grades `partial`). |
| a16637da7249 | 66 (abstract) | "We also construct a sofic group that is not MF, whose canonical trace … is amenable but not quasidiagonal, and a finitely presented torsion-free group with property (T) and no nontrivial homomorphism to an MF group." | amenable half CLOSED on main; torsion-free clause OWNED BY sec5-sentences / census2 U7 (nm-endpoints) | Amenable half: `AmenableTraceTheorem.manuscriptAmenableNonquasidiagonalTrace` (closed, root-imported). The row is graded `partial` only because the torsion-free carrier `TorsionFreePrinted.manuscriptTorsionFreeTheorem` still takes `FournierFacioParagraph` + `HullPrintedInputs` (hgreendlinger, hbridge, hKO, hW) as hypotheses. |

## Routes (no literature input anywhere)

- Elek–Szabó, Theorem 1: `SoficByAmenablePermanence.isSofic_of_isSofic_of_isAmenable_quotient` / `isSofic_of_isSofic_ker_of_isAmenable` / `manuscriptSoficOfSoficKerOfAmenableQuotient`. Proved from Følner sets (`AmenableActionSofic.exists_folner`). Root-imported.
- Locally RF ⇒ sofic: `isSofic_of_locallyResiduallyFinite` (LEFSofic, via LEF).
- Directed unions: `isSofic_of_every_finset_mem_sofic_subgroup` (SoficDirectedUnion). The general directed-family form is `SoficCitationSentences.isSofic_of_directedUnion`, via `Directed.finset_le`.
- Kun/Kun–Thom rigidity step: `isLEF_of_isSofic` (Criterion/CriterionAssembly, root-imported), through `KunFixedDecomposition.expanderDecomposition`.
- V not LEF: `BinaryLeavitt.thompsonV_not_isLEF` (Leavitt/ThompsonVWitness, root-imported).

## Root-wave modules

- `Manuscript/NonMFSentences/AmenableTraceSentencesB.lean`: projection-only carriers; hypotheses are only mathematical (α injective, a ∉ range α); no literature binders. Green unchanged in probes go-lemma42 0911-231324-58545 and sec4-sentences 0911-213033-70201. Not yet in the root; it is in the lead's wave 5 ($NM/msgs/wirecand-093759/wave5.txt).
- `Manuscript/NonMFSentences/BinaryExampleSentences.lean`: the Preusser / Abrams–Aranda / Ara exchange / Aranda–Crow citations are proved unconditionally (`PreusserAssembly.preusser_sandwich`, `BinaryLeavitt.center_eq_bot`, …); EJZ/BHV sentences live in HeadlineCitationSentences (o-preusser). Green in go-lemma42 0911-231324-58545. Wave 5.

## Log

- 2026-09-12: census2 told what this lane owns; cite-kazhdan confirmed de554b7cd342 belongs to cite-sofic.
- 2026-09-12: SoficCitationSentences.lean LANDED NM_UNVERIFIED 3d2a4eac16c7667e09e9816cbb1a854b06d895fe; probe 1 started.
- 2026-09-12: probe 1 PROBE GREEN tag 0912-104415-40292 (BUILT SoficCitationSentences; md5 matches origin). Rows f969236a73d8 and 2c614717a212 CLOSED.
