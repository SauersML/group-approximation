# Conditional content on the non-MF badge surface

What every `\leanverified` badge in `non_mf_groups_exist.tex` actually rests on,
and where the existing gates stop looking.

## Provenance — read this first

> **This sweep ran against a dirty, concurrently edited working tree.**
>
> | | |
> |---|---|
> | Commit | `8e84fb4c8f14fbc0fbcfbc630d1497d0ddf71311` (`8e84fb4c`), branch `main` |
> | Working tree | **dirty**: 15 modified tracked files, 56 untracked, of which **25 are new `.lean` modules** |
> | `non_mf_groups_exist.tex` | modified, and *actively growing during the sweep*: 3836 → 3963+ lines, 94 → 100 `\leanverified` badges |
> | Peers | ten sessions live on this checkout, several writing the very modules catalogued below |
>
> This is not a caveat that weakens the document, it is what makes it
> reproducible. Two consequences, both load-bearing:
>
> 1. **The scan included the in-flight work.** `build_corpus` walks
>    `GroupApproximation/**`, untracked files included, so every one of the 25
>    new modules was in scope. **None of them discharges any item catalogued
>    here** as of this revision — verified directly against the discharge
>    closure, not inferred. Several of them narrow the debt; § 2 says which.
> 2. **Nothing here is keyed to a TeX line number.** Locations are `\label`
>    anchors, section titles, or quoted phrases, and
>    `check_non_mf_unconditional.py` re-locates by anchor on every run (it
>    prints the scan-time line number in parentheses, as a convenience that is
>    expected to go stale). Lean locations are `module:line` and were correct
>    at the revision above.

Scanned corpus: `GroupApproximation/**` (all modules, not only the import
closure), 1073 modules, against `non_mf_groups_exist.tex`. The badge count rose
from 94 to **100** during the sweep; the findings did not move. At the last
run *of that sweep*: **88 unconditional, 12 conditional** (15 findings, rows
1--12), no badge carrying any of the other five certification statuses. Rows
13--14 were off the badge surface. By category, over *declarations*:

| Category | As scanned at `8e84fb4c` | Rows | Now (2026-08-17) |
|---|---|---|---|
| unconditional | 88 | — | every cited declaration |
| conditional-data — undischarged existence package | 3 | 1, 3, 4 | **1** — row 1 discharged; rows 3--4 are off the badge surface, not proved |
| literature-input — published theorem as a quantified premise | 2 | 2, 5 | **0** — both discharged in Lean |
| open — corpus predicate no corpus theorem concludes | 2 | 6, 7 | **0** — discharged, and the anchor was cut |
| *(not mathematical conditionality)* header-hygiene | 4 | 8--11 | **0** — 9--11 fixed in place, 8's anchor cut |
| *(not mathematical conditionality)* category error | 1 | 12 | **0** — the badge moved to a claim |

**Every row of the left-hand column has now been re-verified
declaration-by-declaration, and the right-hand column is the result.** The
interim note that stood here — recording that a gate run exited 0 with zero
findings while only rows 6--7 had been re-read — has done its job and is
retired, as it asked to be. Rows 1 and 18 closed with `D4'`, rows 6--7 with
capstone's instance module, row 13 with the sharpness rewrite, and rows 2, 5
and 8--12 in the pass this table records. Nothing was closed on the strength of
the count.

**Two ways a row leaves this table, and they are not the same.** Rows 1, 2, 5,
6, 7, 9, 10, 11, 12, 13 were *discharged*: a declaration in the tree now proves
what the row said was assumed, or a badge moved onto a claim. Rows 3, 4, 3b and
8 left because the **manuscript stopped citing them** — `prop:stabradical` and
`rem:chaincondition` were cut, and the `\subsection{Questions}` routing datum
is now written as an open question. A detector cannot see a declaration the TeX
does not name, so for those rows an empty gate is not evidence. **Rows 3--4
record mathematics that is still not proved.**

The warrant used throughout is `git cat-file -e origin/verified:<path>`:
presence proves the module went through a green `Build and audit`, since
nothing reaches `verified` without one. Absence proves nothing, because
`verified` runs about a hundred commits behind `main`. Every module named in
rows 2, 5 and 8--12 is present.

So **0 of the badged declarations carry a recorded conditionality finding**,
and the four that carry none only because they are unbadged are named above.
Reproduce with

```
python3 scripts/check_non_mf_unconditional.py --explain      # per-badge verdict
python3 scripts/check_non_mf_unconditional.py --audit-corpus # off-badge watchlist
python3 scripts/check_non_mf_unconditional.py                # the gate (exit 0 since 2026-08-17)
```

---

## 1. The claim being audited, and why it is not what it sounds like

`scripts/check_non_mf_zero_input.py` reports

```
check-non-mf-zero-input: 100 cited declarations are closed
```

That sentence is true and is being read as "100 unconditional mathematical
results". It is not that, in three separate ways.

**(a) It is a check on where the binders are printed, not on what is assumed.**
The whole of its logic is `scripts/check_non_mf_zero_input.py:37-46`: find the
declaration name, and require the next non-space character to be `:`. Both of
these pass:

```lean
theorem closed_and_unconditional :
    ∀ (G : Type) [Group G], P G := …

theorem closed_and_conditional :
    ∀ (semantics : FinitePresentationSemantics Code)
      (_reduction : AdianRabinReduction sourceProperty (mfProperty semantics))
      (_undecidable : ¬ComputablePred sourceProperty),
      ¬ComputablePred (mfProperty semantics) := …
```

The second is `MarkovMFConsequences.operatorMF_recognition_undecidable`, is
badged `\leanverified`, and imports Adian--Rabin as quantified reduction data.
Moving a literature theorem from the header into the proposition changes
nothing about what has been proved.

**(b) It cannot see section `variable`s.** It reads the printed header only.
Four badged declarations sit under an open `variable` command they reference, so
their *elaborated* types have leading inputs that the header does not print --
the very property the gate advertises, false, undetected. `scripts/Audit.lean`
does check this semantically (`hasLeadingInput`, `scripts/Audit.lean:624-628`),
but only for the fifteen names on `zeroInputEndpoints`
(`scripts/Audit.lean:607-622`); none of the four is on that list.

**(c) The `LITERATURE_INPUT` gate is armed and empty.** `Audit.literatureScan`
exists, is calibrated against planted positives and negatives
(`scripts/Audit/Plants.lean:128-170`, `scripts/Calibrate.lean:100-120`), and
fires on any premise mentioning a tagged transcription. Its roster is
`literatureInputNames : List Name := []` (`scripts/Audit.lean:474`). The
mechanism is sound; nothing is on it. That is not an oversight so much as a
mismatch of shape: the corpus does not encode its literature inputs as *named
`Prop`s to be tagged*, it encodes them as **structures carrying the theorem's
conclusion as fields** (`AdianRabinReduction`, `DefectRoutingData`,
`AmenableImpliesMF`), which the roster mechanism was never pointed at.

**One thing the corpus does right, and it should be said plainly:** every one of
these inputs is *visible*. No `sorry`, no `axiom`, no `native_decide`; the
module docstrings say what is not proved, in terms (`MarkovMFConsequences`: "no
Adian--Rabin theorem is asserted as an axiom"; `CliffordBSAmenable`: "**No
inhabitant of this structure is constructed anywhere in this repository**").
The defect is not concealment. It is that `\leanverified` is stamped on top of
the honest prose, and that the automated gates certify the stamp.

---

## 2. Inventory, ranked by how much collapses if never discharged

Status values: **literature-input** (a published theorem enters as data),
**conditional-data** (an existence package the corpus never builds),
**open-predicate** (a corpus predicate no corpus theorem ever concludes),
**header-hygiene** (the advertised closed-header property is false; no
mathematics is at risk), **category** (the badge cites something that asserts
nothing).

"Fix in flight" names an untracked module a peer session was writing during
this sweep. **None of them discharges its item yet** at the revision above;
they are listed so that a later reader treats the item as in progress rather
than as closed or as abandoned.

| # | Declaration | Status | Anchor | Collapse if never discharged | Fix in flight |
|---|---|---|---|---|---|
| 1 | ~~`MarkovMFConsequences.operatorMF_recognition_undecidable`~~ | ~~literature-input~~ → **CLOSED 2026-08-17** | § "Undecidability of MF recognition", prose after `\end{corollary}` of `cor:undecidable` | **None.** Unconditional Lean support exists: `Computability.operatorMF_recognition_not_computable` (`Computability/BooneWordProblemUndecidable.lean`) concludes `¬ ComputablePred (MarkovMFConsequences.operatorMFProperty PresentationCodes.semantics)` outright — no reduction datum, no Markov hypothesis, no literature input. It is `AdianRabinVariantTransform.operatorMF_recognition_undecidable_of_wordProblem` applied to `Computability.not_computablePred_wordProblemPred`, which is `D4'` closed: the word map is `BooneWords.rawComm`, computable by `Computability.computable_rawComm`, and agreement with halting is `Computability.wordProblem_rawComm_iff` composed with `Computability.commElt_eq_one_iff_halts`, packaged as `Computability.exists_boone_words`. The quantified `operatorMF_recognition_undecidable` remains badged in the TeX as the classical form of the conclusion, with the Markov data quantified rather than exhibited; it is no longer the corollary's only support, so the finding it recorded is discharged rather than accepted. | Closed — `Computability/BooneWords.lean`, `BooneWordMapPrimrec.lean`, `BooneWordAgreement.lean`, `BooneWordProblemUndecidable.lean` |
| 2 | ~~`ContinuumMultiplicity.manuscriptContinuumMultiplicity`~~ → **CLOSED 2026-08-16** | § "Undecidability of MF recognition", multiplicity paragraph citing `\cite{Neumann37}` | **None.** The family is constructed: `Monsters/NeumannContinuum`, lamplighters over coset spaces of the free group. **Re-verified 2026-08-17**, declaration by declaration: `manuscriptContinuumMultiplicity` is a three-way conjunction whose second conjunct *exhibits* a continuum of pairwise nonisomorphic finitely generated groups and whose third is the printed headline with nothing assumed, both discharged from `NeumannContinuum.manuscriptContinuumMultiplicityUnconditional`. It is zero-input, badged at one site, inside the import closure, and `Sofic/ContinuumMultiplicity` and `Monsters/NeumannContinuum` are both on `origin/verified`. The `Neumann37` citation survives in the manuscript as attribution for the classical family, not as a step. | Closed — the badged declaration now exhibits the family as a conjunct; see §2 |
| 3 | `FullMFRadicalEndpoint.exists_nontrivial_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical` | **NOT DISCHARGED**, off the badge surface (2026-08-17; was `conditional-data`) | nothing — the § "Questions" material it answered was deleted from the TeX | **None on the printed surface.** The datum is still unbuilt, but no printed sentence consumes the endpoint, so it exposes nothing. See §3–4 | `notes/HULL_ROUTING_AUDIT_2026-08-16.md` (the reduction to one certificate — **protect this**); `Sofic/FiveConditionInsufficiency.lean`; `Sofic/ConcreteCompressionSource.lean` (7 of 12 fields built) |
| 4 | `FullMFRadicalEndpoint.exists_nontrivial_group_with_every_nontrivial_quotient_not_isCDEOperatorMF` | **NOT DISCHARGED**, off the badge surface (2026-08-17; was `conditional-data`) | same | as above | same |

**Rows 3–4, the six-condition correction of 2026-08-16.** The manuscript now
prints **six** conditions, not five: it adds "`q` does not kill the
distinguished element of the datum, so that `Q ≠ 1`", and states in print that
this sixth condition does not follow from the other five. That is exactly the
field `DefectRoutingData.protected_ne_one`, so `DefectRoutingData` is now 1:1
with the printed hypothesis list, and the endpoints badged at that sentence are
the `exists_nontrivial_*` pair, which conclude `Nontrivial Q`. Rows 3–4 are
repointed accordingly; the former declaration names are no longer cited
anywhere in the TeX.

`FiveConditionRoutingData` did not disappear — it now models "the other five",
the object of the printed insufficiency paragraph, and
`FiveConditionInsufficiency.trivialQuotient` inhabits it with the trivial group
for every defect datum. That is what rows 3a and 3b certify.

The rows stay `conditional-data` because `DefectRoutingData` and
`FournierFacioDefectData` are built nowhere in the corpus —
`Sofic/ConcreteCompressionSource.lean` deliberately builds only the weaker
`CompressionSourceData`, which has no simple subgroup and no property-(T)
field.

Rows 3–4 were audited against the literature on 2026-08-16
(`notes/HULL_ROUTING_AUDIT_2026-08-16.md`, read from Hull, *Small cancellation
in acylindrically hyperbolic groups*, Groups Geom. Dyn. 10 (2016) 1077–1119,
and Osin, *Acylindrically hyperbolic groups*, Trans. AMS 368 (2016) 851–888).
Six of the seven fields of `DefectRoutingData` are supplied by Hull's Theorem
7.1 as published — including finite presentation, since that theorem adjoins the
cyclic shifts of one word per prescribed element, and including two-generation
and defect surjectivity, which are the same clause once the suitable subgroup is
chosen two-generated inside the defect.  The undischarged input is a single
certificate: one infinite-order element of the compression defect generating a
hyperbolically embedded cyclic subgroup (Hull, Lemma 5.8), equivalently a
suitable subgroup inside the defect.  The Bass–Serre action of the ascending HNN
skeleton cannot supply it, since that action fixes the end of the telescope and
an acylindrical action is never quasi-parabolic (Osin, Theorem 1.1); Hull's own
HNN result (Proposition 6.2) covers extensions over cyclic subgroups, not over
the whole Kazhdan base.  These rows therefore stay, with that sharper reason.
| 5 | ~~`ClosedEnvelopeCompression.manuscriptEnvelopeCompressionBlind`~~ → **CLOSED 2026-08-16** | `rem:chaincondition`, Zariski-envelope sentence | **None.** The chain condition is proved: `Algebra/ZariskiDescendingChain.wellFoundedLT_isZClosedSubgroup`, from the Hilbert basis theorem. **Re-verified 2026-08-17, and it is now closed twice over.** The mathematics: `Algebra/ZariskiDescendingChain` is in the import closure and on `origin/verified`. The print: `rem:chaincondition` **no longer exists in the manuscript** — the label occurs zero times, the string `Zariski` occurs zero times, and `manuscriptEnvelopeCompressionBlind` has zero badge sites. There is no longer a printed sentence quoting the chain condition as classical, so there is nothing left for this row to be a finding about. | Closed — the badged declaration now exhibits the `Closed` package as a conjunct; see §5 |
| 6 | `MatricialStabilityRadical.actualCoronaMFResidual_eq_fdUnitaryResidual` | **discharged** | *(target cut from the tex)* | Premise inhabited with no literature input by `MatricialStabilityInstances.{freeGroup,multiplicativeInt}_isPointNormMatriciallyStable`, and clause 2 applied at both; `prop:stabradical` itself was cut by `3a45fa60`, so nothing badges this. | — |
| 7 | `MatricialStabilityRadical.not_isCDEOperatorMF_of_stable_of_fdResidual_ne_bot` | **discharged** | *(target cut from the tex)* | As row 6, but discharged in the *contrapositive*: the forward direction (stable + nontrivial fd residual ⟹ non-MF) is exercised by no corpus group, and both stable witnesses provably have `fdUnitaryResidual = ⊥`. | — |
| 8 | ~~`MatricialStabilityRadical.actualCoronaMFResidual_le_fdUnitaryResidual`~~ | ~~header-hygiene~~ → **CLOSED 2026-08-17** | ~~`prop:stabradical` clause 1~~ — the anchor is gone | **None, and now for the second of two independent reasons.** The binders were moved after the colon on 2026-08-16 (see the status table below), and the declaration is verified zero-input today. Since then `prop:stabradical` was cut from the manuscript entirely: the label occurs **zero** times and this declaration has **zero** badge sites, which is the same reason rows 6--7 fell. `Sofic/MatricialStabilityRadical` is on `origin/verified`. A finding needs a badge to be a finding about. | — |
| 9 | ~~`MarkedGroupSpace.isClosed_operatorMFLocus`~~ | ~~header-hygiene~~ → **CLOSED 2026-08-17** | `thm:markedclosed`(1) | **None.** Fixed in place rather than by retreat: the anchor still exists, the declaration is still badged at one site, and it is verified zero-input at the current sha. `Sofic/MarkedMFClosed` is on `origin/verified`. | — |
| 10 | ~~`MarkedGroupSpace.isOpen_compl_operatorMFLocus`~~ | ~~header-hygiene~~ → **CLOSED 2026-08-17** | `thm:markedclosed`(2) | **None.** Same anchor, same module, same three checks, same result. | — |
| 11 | ~~`QuasiRegularWitness.baseVector_apply_base`~~ | ~~header-hygiene~~ → **CLOSED 2026-08-17** | `rem:maxinfinite` | **None.** `rem:maxinfinite` survives, the badge is at one site, the declaration is verified zero-input, and `Analysis/QuasiRegularWitness` is on `origin/verified`. | `Analysis/ResiduallyFiniteDimensional.lean` works on the same remark (different clause) |
| 12 | ~~`ManuscriptExactWrappers.ManuscriptHSInvisible`~~ | ~~category~~ → **CLOSED 2026-08-17** | `def:invisible` | **None, and the badge move that was pending has landed.** `ManuscriptHSInvisible` — the definition — has **zero** badge sites. `def:invisible` now badges `manuscriptHSInvisibleCharacterization`, `CLAIM_TARGETS["def:invisible"]` points at it, and `notes/NON_MF_NUMBERED_CLAIMS.json` records it as covering "the complete printed proposition". So the badge certifies a claim, which is the whole of what this row asked for. `Sofic/ManuscriptExactWrappers` is on `origin/verified`. | — |
| 13 | `CliffordBSAmenable.isOperatorMF_subgroup_CliffordBS` | **RESOLVED 2026-08-17** (was: literature-input, off-badge) | `\paragraph{Sharpness of the Kazhdan hypothesis.}` | **None.** The paragraph no longer deduces through amenability; it routes through exhibited monomial models and is badged `\leanverified` over `CliffordBSAmenableMF.manuscriptSharpnessOfKazhdanHypothesis`, which is on `origin/verified`. The Lean structure survives, cited by nothing. What stays conditional is one clause, `IsOperatorMF RealizedQuotient`, as a binder in `CliffordBSPrintedRoute` — the printed route, kept deliberately. See §13 | `Sofic/CliffordBSAmenableMF.lean` supplies it; `Algebra/AmenableMFProof.lean`, `Analysis/AmenableQuasidiagonal.lean` explain why no permutation route could |
| 14 | ~~`HNNTorsionFree.isPowerTorsionFree_of_existsCyclicConjugate` (and `…_sourceGroup_…`, `…_integerSourceGroup_…`)~~ | ~~literature-input~~ → **CLOSED 2026-08-16** | none — no manuscript claim cites it yet | **None.** `ExistsCyclicConjugate` is now proved, not assumed: `HNNBritton.existsCyclicConjugate` (`GroupTheory/HNNBrittonCyclic.lean`, commit `ae4053f7`) discharges it for every `φ` from Mathlib's HNN normal-form theory. The three hypothesis-taking theorems remain only because that file imports `Algebra/HNNTorsionFree.lean` (invoking it there would be an import cycle); they are superseded one for one by `HNNBritton.isPowerTorsionFree_hnn`, `…_sourceGroup`, `…_integerSourceGroup`. | — |
| 15 | ~~`NuclearityAmenability.not_isAmenable_of_base_embeds`~~ | ~~header-hygiene~~ → **CLOSED 2026-08-16** | `thm:D`, the non-nuclearity paragraph | **None.** The manuscript now badges the wrapper `manuscriptNotAmenableOfBaseEmbeds`, whose binders are all after the colon, so the finding is gone rather than accepted. | — |
| 16 | ~~`SoficByAmenablePermanence.isSofic_of_isSofic_ker_of_isAmenable`~~ | ~~header-hygiene~~ → **CLOSED 2026-08-16** | `\paragraph{Extensions by $\Z$.}` | **None.** Superseded by the badged wrapper `manuscriptSoficOfSoficKerOfAmenableQuotient`. | — |
| 17 | ~~`ZariskiClosedSubgroup.manuscriptZariskiClosureOfRepresentation`~~ | ~~header-hygiene, open-variable~~ → **CLOSED 2026-08-16** | `rem:chaincondition` | **None.** Superseded by `manuscriptZariskiRepresentationEnvelopeClosed`, which binds `n`, `k` and the field instances after the colon, so the open-variable half is closed too.  Row 5 on the same remark is a genuine literature input and stays. | — |
| 18 | `MarkovMFConsequences.presentationCodes_recognition_undecidable_of_haltingReduction`, `…_negative_side_not_re_of_haltingReduction` | conditional-data, buried-conditional | `cor:undecidable`, the two badges under the corollary | **None for the print/Lean relation, which is the thing this document audits.** Row 1's reduction is here an *explicit hypothesis*, and `cor:undecidable` is printed conditional in as many words — "suppose given a computable map sending each instance of the halting problem to a presentation code whose group is MF exactly when that instance halts". Badge and printed statement therefore have the same strength. What collapses if the reduction is never built is the *unconditional* undecidability of MF recognition, which row 1 already tracks and which the manuscript does not claim. The `buried-conditional` half names `haltingProperty` under the same premise; that is the halting problem, named, not a second input. **Update (2026-08-16):** these two now take the printed data directly --- the transform, `Computable transform`, and the correctness equivalence --- and build the `AdianRabinReduction` internally from the closed `PresentationCodes.markovWitness`, so the badge matches the printed hypothesis exactly rather than asking for a Markov witness the prose never grants. The `conditional-data` detector consequently stops firing on them (a hypothesised plain function is not a corpus-defined structure) and the two baseline lines were removed; the conditionality itself is unchanged, is printed in the corollary, and is recorded by ledger rows UN.02/UN.03 and by the surviving `buried-conditional` lines. **Update (2026-08-17): the hypothesis is discharged, and these two declarations have left the badge surface.** The reduction the row asks for is now built and applied: `Computability.not_computablePred_wordProblemPred` (`Computability/BooneWordProblemUndecidable.lean`) proves the uniform word problem on presentation codes undecidable outright, by supplying the Boone word map — `BooneWords.rawComm` as raw data in the code's own numbering, `Computability.computable_rawComm` for its computability, `Computability.exists_boone_words` for agreement with halting — to the join in `UniformWordProblemUndecidable`. `Computability.operatorMF_recognition_not_computable` is that fed through `AdianRabinVariantTransform.operatorMF_recognition_undecidable_of_wordProblem`. The printed corollary changed with it: its first assertion is now "`W` is undecidable, and no algorithm decides MF from a presentation code", with no premise, and the quoted "suppose given a computable map…" wording is no longer in the TeX. Separately, and for an unrelated reason, `presentationCodes_recognition_undecidable_of_haltingReduction` and `…_negative_side_not_re_of_haltingReduction` are cited nowhere in `non_mf_groups_exist.tex` any more (verified, zero occurrences), so the `buried-conditional` detector no longer reaches them and their two baseline lines were deleted as stale rather than as discharged. **Second update, same day: the negative-side clause went too.** `WordProblemRE.rePred_wordProblemPred` proves `W` recursively enumerable with no hypothesis, by writing both sides of the certificate check as raw words and witnessing free triviality with a deletion sequence — the repair `AdianRabinWordProblem`'s docstring had scoped and could not reach, because the natural certificate lives in a free group whose type depends on the code. An undecidable r.e. predicate has a non-r.e. complement, so the printed clause is now unconditional as well and `cor:undecidable` carries no hypothesis at all. A packaging gap was recorded here briefly — the composition was a term rather than a named declaration — and it is now closed: the hypothesis-taking forms were renamed to `…_of_not_computablePred` and argument-free wrappers `WordProblemRE.not_rePred_compl_wordProblemPred` and `WordProblemRE.operatorMF_negative_side_not_re` added, both badged at the corollary. Nothing at `cor:undecidable` is conditional on anything. | `Computability/AdianRabinMarkovProperty.lean` and `Computability/HaltingReduction.lean` — the first certifies the Markov hypotheses, the second the reduction interface; neither constructs an `AdianRabinReduction`.  Superseded 2026-08-17 by `Computability/BooneWordProblemUndecidable.lean` and `Computability/WordProblemRE.lean`, which construct nothing of the sort and do not need to: between them they discharge the two hypotheses `AdianRabinVariantTransform` had left |
| 19 | ~~`kt_06_ultraproduct_finite`, `kt_10_finiteness_reverses`~~ | ~~header-hygiene~~ → **CLOSED 2026-08-16** | `lem:ultrafinite`, `lem:finitecompare` | **None mathematically**, and now nothing to accept: both are fixed in place by the rows 8--11 method, binders after the colon and a leading `intro`. These two badges arrived with the Step 6 rewrite of `thm:collapse` and were never on the baseline. `kt_10` had no section variables at all; `kt_06` draws `(Z : ℕ → FiniteModel)` and `[∀ n, Nonempty (Z n)]` from the `Polar` section block, and they are restated in that order, so the elaborated type does not move. | — |

### Status, 2026-08-16: rows 8--12 and the gate

The sweep above is a snapshot and is left as recorded.  What has moved since:

| # | Now | Where |
|---|---|---|
| 8 | **fixed.** `∀ {G : Type u} [Group G], …` inside the proposition; proof unchanged apart from a leading `intro G _` | `Sofic/MatricialStabilityRadical.lean` |
| 9 | **fixed.** `∀ {k : ℕ}, …`; proof unchanged apart from `intro k` | `Sofic/MarkedMFClosed.lean` |
| 10 | **fixed.** likewise, and its one-line proof now names the rank explicitly | same |
| 11 | **fixed.** `∀ (G : Type u) [Group G] (K : Subgroup G) [DecidableEq (G ⧸ K)], …`; same elaborated type as before, now printed | `Analysis/QuasiRegularWitness.lean` |
| 12 | **DONE 2026-08-17** *(this cell read "Lean side landed, badge move pending"; the move has since landed — see row 12 above)*. **Lean side landed, badge move pending.** `ManuscriptExactWrappers.manuscriptHSInvisibleCharacterization` states what a badge on `def:invisible` can honestly certify: fidelity of the predicate to the printed text, the identity of that predicate with the `hDkill` premise of `thm:abstract-nk`, and that invisibility is a subgroup condition. The badge and `CLAIM_TARGETS["def:invisible"]` still point at the definition | `Sofic/ManuscriptExactWrappers.lean` |

None of the four restatements changes an elaborated type, so no printed
statement moves and no manifest hash changes.  Rows 8--11 were fixed by moving
the binders, **not** by adding the names to `Audit.zeroInputEndpoints`: that
list is checked by `hasLeadingInput`, which reports *any* leading `forallE`, so
a name on it must have no outer telescope at all -- its universal sentence has
to be routed through a named closed `Prop`.  The alternative offered in § 8--11
above is therefore not available as stated; the four names would fail that
audit in their fixed form.

The gate is armed against regression rather than against the backlog:
`scripts/check_non_mf_unconditional.py --baseline` reads
`notes/NON_MF_UNCONDITIONAL_BASELINE.txt`, an itemized register of the findings
this document records.  A finding not on it fails; an entry that matches
nothing fails too, so a discharged row cannot leave its exemption behind.
There is no count in the mechanism and `--strict` ignores the register
entirely, which is the end state once rows 1--7 land.

**The register is empty as of 2026-08-17, and `--baseline` and `--strict`
now agree**: every cited declaration is reported unconditional, and no
finding of any status is raised. That is not the same as rows 1--7 having
landed, and the distinction is the whole point of keeping § 2 as prose.

* **Discharged.** Row 1: `Computability.operatorMF_recognition_not_computable`
  proves MF recognition undecidable with nothing quantified. Rows 2, 5,
  14--17 and 19 closed on 2026-08-16, each on its own mathematics.
* **Fixed in place.** Rows 8--11 by moving binders after the colon; row 12 by
  moving the badge from the definition to
  `manuscriptHSInvisibleCharacterization`, which is now the declaration
  `def:invisible` cites (verified in the TeX).
* **Off the badge surface, not proved.** Rows 3, 4, 3b, 6, 7 and 18 name
  declarations that occur **zero** times in `non_mf_groups_exist.tex` after
  the 2026-08-17 restore (verified by grep, name by name). A detector that
  cannot see a declaration reports nothing about it, so the register's
  silence about them is not evidence. Row 13 was never on the badge surface
  at all and is unaffected.

Use the register only to answer "would the gate fail today". For "what is
still conditional", read the rows.

### Cross-check against the manuscript's own prose

**As taken (2026-08-16.)** Grepping the `.tex` for self-declared
conditionality (`quantifies over`, `not formalized`, `literature input`,
`as a hypothesis`, `conditionally on`, `not an unconditional`) returned
exactly **four** sites, and all four were rows above: `rem:chaincondition`
(row 5), the `cor:undecidable` discussion (row 1), the Neumann paragraph
(row 2), the `\subsection{Questions}` routing datum (rows 3--4). A fifth
hit, at `def:radical` — "that is the form the formalization quantifies
over" — was benign: it names the definitional variant, and the equivalence
is itself proved (`prop:mf-equivalences`).

The manuscript, in other words, already knew about four of these and said so
in print. In all four cases the sentence admitting the condition sat within a
few lines of a `\leanverified` badge.

**Re-run 2026-08-17: the same grep now returns one site, and it is not a
caveat.** The single hit is "with no hypothesis and no literature input" in
the `cor:undecidable` discussion — a claim that something *is*
unconditional, which is true and is row 1's closure. The other four sites
went for three different reasons, and only one of them is mathematics:

* row 1's caveat is gone because the hypothesis is discharged;
* rows 2 and 5's caveats went with their 2026-08-16 closures;
* rows 3--4's caveat went because the `\subsection{Questions}` item is now
  written as an open question with a route sketch — "What remains is
  group-theoretic: a torsion-free finitely presented group whose subgroup
  `N_conj` contains a *nontrivial* normal property-(T) subgroup" — and no
  longer announces a conditional answer, so there is no conditional
  statement left to caveat and no `exists_nontrivial_*` badge on it.

This is the one place where an empty grep is the wrong signal to trust. The
manuscript stopped claiming the conditional results; it did not acquire
unconditional ones. Rows 3--4 record what is still not proved.

### 1. Adian--Rabin as quantified reduction data

`GroupApproximation/Computability/MarkovMFConsequences.lean:112`

```lean
theorem operatorMF_recognition_undecidable :
    ∀ {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
      {sourceProperty : Source → Prop}
      (semantics : FinitePresentationSemantics Code)
      (_reduction : AdianRabinReduction sourceProperty
        (operatorMFProperty semantics))
      (_source_undecidable : ¬ComputablePred sourceProperty),
      ¬ComputablePred (operatorMFProperty semantics)
```

The conditional content is `AdianRabinReduction`
(`MarkovMFConsequences.lean:55-63`): a structure whose fields are a Markov
witness, a code transformation, `Computable transform`, and the correctness
equivalence `targetProperty (transform source) ↔ sourceProperty source`. Those
fields *are* the Adian--Rabin theorem. Nothing in the corpus constructs one,
and the file says so: "No inhabitant is postulated in this file."

**Update (2026-08-16).** The excerpt above is the shape at the revision this
inventory was taken. Two things have since moved, neither of them the
conditionality this row records. The interface (`MarkovWitness`,
`FinitePresentationSemantics`, `operatorMFProperty`, `AdianRabinReduction`, and
the two pullback lemmas) now lives in
`Computability/MarkovReductionInterface.lean`, under the same namespace; and
`operatorMF_recognition_undecidable` no longer quantifies over `Code` and
`semantics` but is stated at `PresentationCodes.semantics`, because the
manuscript prints the corollary in the recursive coding and the paragraph after
it disavows the arbitrary-semantics reading. The `AdianRabinReduction` premise
is untouched, and the gate still reports this row.

Standing in for: Rabin 1958 / Adian, the unsolvability of Markov properties of
finite presentations.

Depends on it: `cor:undecidable`, which is printed unconditionally ("There is
no algorithm that decides, from a finite presentation, whether the presented
group is MF"). The following paragraph is honest — "This corollary carries one
classical literature input… which we have not formalized" — and then the badge
on the next line is `\leanverified`.

Not conditional, and correctly so: `FinitePresentationSemantics` in the same
telescope. `PresentationCodes.semantics` builds one
(`GroupApproximation/Computability/PresentationCodes.lean:109`), so the coding
half is genuinely formalized. `operatorMF_subgroup_hereditary` and
`exists_finitelyPresented_nonOperatorMF`, badged in the same paragraph, are
unconditional. Exactly the group-theoretic half the prose claims.

### 2. B. H. Neumann's continuum family as a quantified premise

`GroupApproximation/Sofic/ContinuumMultiplicity.lean:246`

```lean
theorem manuscriptContinuumMultiplicity :
    ∀ {ι : Type} (N : ι → Type) [∀ i, Group (N i)] [∀ i, Group.FG (N i)],
      (∀ i j : ι, Nonempty (N i ≃* N j) → i = j) →
        Cardinal.mk ι = Cardinal.continuum → …
```

**CLOSED 2026-08-16.**  The snippet and description above are the state before
the construction landed, and are kept only so the closure is legible.

What was said: no corpus-defined name appears, so the structural rule cannot
see it; the premises jointly *are* Neumann 1937; the corpus never exhibits such
a family; and the module docstring said so.

What is true now: the corpus builds one.  `Monsters/NeumannAlternatingFamily`
constructs `A₅ ≀_{F₂/markedSubgroup S} F₂` for every `S ⊆ ℕ`, and
`Monsters/NeumannContinuum.neumann_continuum_of_finitely_generated_groups`
extracts a continuum-sized pairwise nonisomorphic transversal by the same
countable-fibres argument the manuscript uses one level up.  Neumann's sharper
two-generator form is not needed — the counting step consumes only `Group.FG` —
so nothing is quoted anywhere in the chain.

`manuscriptContinuumMultiplicity` was restructured to *state* that, rather than
have a second declaration badged beside it: it is now three conjuncts with no
premises — the deduction (the half the manuscript says "uses only that the `N`
are finitely generated"), the existence of the family, and the unconditional
headline.  The counting step moved one module up to
`Sofic/ContinuumMultiplicityCore`, under the same namespace, so the badged
declaration could sit downstream of the construction; callers were unaffected.
The hand-written `KNOWN_CONDITIONAL_DECLARATIONS` entry was deleted.

What is genuinely proved on top of it is the manuscript's own counting step
(countable groups have countably many f.g. subgroups, so the fibres are
countable) — real content, and the honest badge for it is `\leanpartial` or
`\leanconditional`, not `\leanverified`.

### 3--4. The routing datum — **NOT DISCHARGED**, and off the badge surface

**Read this heading against §6--7.** Those rows say DISCHARGED and off the badge
surface; these say the opposite about the first half and the same about the
second, and the difference is the whole point. Rows 6--7 and 13 were rows
describing a corpus that had moved underneath them. **These are not.** The
packages below are still unbuilt, and the route to them has closed rather than
opened. What changed is only that the manuscript **stopped claiming** the
conditional results — it did not **acquire** unconditional ones. An empty grep is
the wrong signal to trust here; that is why these rows stay, regraded rather than
deleted.

**Off the badge surface (2026-08-17).** `Hull`, `FullMFRadicalEndpoint`,
`DefectRoutingData`, `orderPreserving_quotient_not_subsingleton` and
`\leanconditional` each occur **zero** times in `non_mf_groups_exist.tex`, and
there is no `\bibitem` for Hull. The § "Questions" item that rows 3--4 answered
now asks the question and answers nothing: its only badge is
`finiteSubgroup_eq_bot_of_isMulTorsionFree`, which is unconditional and unrelated
to the routing program. So the endpoints are conditional Lean that no printed
sentence consumes, and they expose nothing on the trust surface. Row 3b was
dropped in the same pass, per its own note: its printed sentence ("would supply
the sixth condition") was deleted a day earlier at `8b16a847`, whose commit
message records that the badge never supported the claim.

**Why the route is closed, twice over.** This is the part to read before anyone
reopens it.

* *Inadmissible.* The only known route is the one
  `notes/HULL_ROUTING_AUDIT_2026-08-16.md` reduces it to, and discharging the
  package by quoting Hull's Theorem 7.1, Hull's Lemma 5.8 or Osin's Theorem 1.1
  is a literature-transcription premise. The standing zero-literature order keeps
  `Audit.literatureInputNames` empty — the roster's own docstring states the
  prohibition — so a citation route is not a legal closing move, whatever its
  quality.
* *Unavailable.* Proving those results here is not a lemma but a library. The
  pinned Mathlib has **no** acylindrical hyperbolicity, **no** hyperbolically
  embedded subgroups, **no** small cancellation and **no** Greendlinger: a grep
  over `Mathlib/` at the pin for `acylindric`, `hyperbolically embedded`,
  `smallCancellation` and `Greendlinger` matches zero files. That is a
  from-scratch geometric group theory development, comparable to or larger than
  the routing layer it would serve.

**The asset to protect.** `notes/HULL_ROUTING_AUDIT_2026-08-16.md` reduces the
whole problem to a single certificate — one infinite-order `h ∈ N_comp` with
`⟨h⟩` hyperbolically embedded and properly contained in `N_comp` — after which
six of the seven `DefectRoutingData` fields fall out of Hull's Theorem 7.1 as
published, with property (T) supplied by a torsion-free finitely presented
Kazhdan uniform lattice. It also proves the Bass--Serre action of the skeleton
**cannot** supply that certificate, since an acylindrical action is never
quasi-parabolic. That reduction is real work and survives this regrade; it is
findable at that path and should not be lost in any cleanup.

**How far the packages are actually built**, so nobody re-derives it:

* `ConcreteCompressionSource.sourceData` (`:353`) and `integerSource` (`:413`)
  build `CompressionSourceData` unconditionally — that is
  `FournierFacioDefectData` minus `kazhdan`, `simpleSubgroup`, `simple`, `s_mem`
  and `witness_mem`, so **7 of 12 fields are done**.
* But `integerSource`'s base is `Multiplicative ℤ`, infinite and amenable, so it
  can **never** carry property (T). That specialization is a **permanent dead
  end, not a near miss**; a different source is required.
* `OrderPreservingRoutingData.sourceTorsionFree` is fully closed for the concrete
  skeleton by `HNNBrittonCyclic.isPowerTorsionFree_integerSourceGroup` (`:347`).
  `quotient_surjective` follows from `defect_surjective`; `torsionFree` and
  `protected_ne_one` both follow from `orderPreserving`.
* **`orderPreserving` itself has no candidate anywhere in the tree.** That is the
  hard field, and it is where an attempt would actually stall.

**The layer stays.** It compiles, it is on `origin/verified`, it is a legitimate
data-parameter layer with no premise exposure, and it is the honest record of a
real research route. Deleting certified work to tidy a count is not something
this repository does. The guardrail is the off-print grade here plus the banners
on `notes/TORSION_FREE_HULL_ROUTE.md` and
`notes/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md`, which together make
promotion to a numbered environment impossible without deliberately overriding a
written prohibition.

The original assessment follows, unchanged and still accurate about the Lean.

`GroupApproximation/Sofic/FullMFRadicalEndpoint.lean:32` and `:55`, both with

```lean
    ∀ {P : Type} {E : Type u} [Group P] [Group E]
      {D : FournierFacioDefectData P E}
      (_h : Nonempty (DefectRoutingData.{u} D)), …
```

Two undischarged packages, not one:

* `FournierFacioDefectData` (`Sofic/TorsionFreeFullMFRadical.lean:68`) — the
  HNN skeleton of Fournier-Facio, as proof-carrying algebraic data. **Never
  constructed anywhere in the corpus**, in any specialization.
* `DefectRoutingData` (`Sofic/TorsionFreeFullMFRadical.lean:231`) — Hull's
  relative small-cancellation output. It *is* produced, by
  `SmallCancellationRouter.RoutingLemmaData.toDefectRoutingData`
  (`Sofic/SmallCancellationRouter.lean:314`), which consumes a
  `RoutingLemmaData`, which nothing produces. One further link back,
  `GreendlingerGate` (`SmallCancellationRouter.lean:215`) — the classical
  metric small-cancellation theorem — is consumed as an explicit hypothesis.
  The chain is open end to end.

  A single-step "is it produced?" test reports `DefectRoutingData` as
  discharged and is wrong. The gate computes discharge as a least fixed point
  for this reason.

Standing in for: Fournier-Facio's construction, plus a strengthening of Hull's
common-quotient theorem that does not exist in the literature yet
(`SmallCancellationRouter`'s docstring: "the hoped-for bespoke
small-cancellation lemma").

Depends on it: the open-problem list's answer to "Is there a torsion-free
finitely presented non-MF group?". The prose is scrupulous — "It is that
implication, with the routing datum as a hypothesis, that the two badges below
certify; neither is an unconditional statement" — and then uses
`\leanverified` twice.

### 5. The Zariski descending chain condition

`GroupApproximation/Criterion/ClosedEnvelopeCompression.lean:116`

```lean
theorem manuscriptEnvelopeCompressionBlind :
    ∀ {G : Type} [Group G] (Closed : Subgroup G → Prop),
      (∀ (g : G) (H : Subgroup G), Closed H →
          Closed (H.map (MulAut.conj g).toMonoidHom)) →
        ∀ [WellFoundedLT {H : Subgroup G // Closed H}] …
```

**CLOSED 2026-08-16.**  The description above is the state before the Zariski
machinery landed, and every clause of it is now wrong; it is kept only so the
closure is legible.

What was said: the two premises jointly *are* the classical theorem that
Zariski closed subgroups of `GL(V)` satisfy the descending chain condition, the
corpus exhibits no `Closed` for which the instance holds, and
`Algebra/ZariskiDescendingChain` "does not exist at this revision".

What is true now:

* `Algebra/ZariskiDescendingChain` exists, compiles, and proves
  `wellFoundedLT_isZClosedSubgroup` as an `instance`, from the Hilbert basis
  theorem through the ideal--variety pair — the ground `rem:chaincondition`
  names.
* `Algebra/ZariskiEnvelopeEndpoint.manuscriptZariskiEnvelopeData` exhibits the
  whole premise tuple at it, so the corpus does exhibit a `Closed`.
* `manuscriptEnvelopeCompressionBlind` was restructured so that it *states* the
  discharge rather than leaving it beside: it is now three conjuncts with no
  premises — the abstract principle, the inhabitation of that principle's
  premises for `GL n k` over any field, and the displayed identity
  `closure of σ(tΓt⁻¹) = closure of σ(Γ)` for an arbitrary representation.
* The hand-written `KNOWN_CONDITIONAL_DECLARATIONS` entry was deleted.
* The sentence attributed to `rem:chaincondition` above — "is the input the
  badge quantifies over rather than proves" — **does not occur in the
  manuscript** and appears to have been transcribed from an early draft.  The
  remark says only that the chain condition comes "from the Hilbert basis
  theorem".  The same fabricated quote had been copied into the gate roster and
  into `ZariskiDescendingChain`'s own docstring; both are corrected.

### 6--7. Point-norm matricial stability — **DISCHARGED**, and off the badge surface

`GroupApproximation/Sofic/MatricialStabilityRadical.lean:182` and `:193`,
premise `IsPointNormMatriciallyStable G` (defined at `:48`).

**Both rows are closed, on two independent grounds.** Recorded 2026-08-17
against `origin/main` `0ed335cd`; the line numbers above are current at that
revision, and the ones this section previously carried (`:175`, `:186`, `:40`)
had drifted.

**The premise is inhabited, and proved so with no literature input.**
`GroupApproximation/Sofic/MatricialStabilityInstances.lean` concludes it twice:

| Theorem | Statement |
|---|---|
| `freeGroup_isPointNormMatriciallyStable` (`:359`) | `∀ α : Type u, IsPointNormMatriciallyStable (FreeGroup α)` |
| `multiplicativeInt_isPointNormMatriciallyStable` (`:393`) | `IsPointNormMatriciallyStable (Multiplicative ℤ)` |

Neither imports anything. The free-group proof takes the genuine
representations to be `FreeGroup.lift fun a ↦ B.map n (FreeGroup.of a)` — the
universal property — so they agree with the almost representation *exactly* at
the generators, and the estimate propagates along words because the tracking
locus is a subgroup (`:324`--`:350`). `ℤ` is the same construction through
`intPowerHom`. No averaging, no repair, no functional calculus, and in
particular no Eckhardt--Shulman: the earlier text's assumption that the
witnesses had to come from the literature was simply wrong, because free groups
have no relations to preserve.

**And both clauses are applied.** Clause 2 at `:446` (free groups) and `:479`
(the integers); clause 3 at `:459` and `:491`. `stabilityHypothesis_inhabited`
(`:500`) bundles an inhabitant with both consequences, and says in its own
docstring that it exists so this row can be closed by pointing at one name.

**Claim strength, stated exactly.** Clause 3 is discharged *in the
contrapositive*: the corpus uses it as "stable and MF, therefore
`fdUnitaryResidual = ⊥`", which is how countable free groups are shown
residually finite dimensional. The forward direction — stable with a
nontrivial finite-dimensional residual, therefore not MF, the direction that
would manufacture a new non-MF group — is exercised by **no corpus group**, and
both stable witnesses provably have `fdUnitaryResidual = ⊥` (`:452`, `:485`).
The gate's criterion is satisfied and the clause is not dead weight, but it has
never been run in the direction the manuscript wanted it for.

**Independently, the printed target no longer exists.** `prop:stabradical`
occurs in no `.tex` file in the repository; it was cut by `3a45fa60`
("Editorial pass: rewrite orbit collapse, cut what nothing uses"). Neither
declaration is cited by any badge, and no surviving `\label` matches `stab`, so
these rows are outside this document's own scope — what every `\leanverified`
badge rests on — regardless of the mathematics above.

**Why this sat stale.** `MatricialStabilityInstances.lean` was created by
`892665dc`, which post-dates this document's scan revision `8e84fb4c`
(`git cat-file -e 8e84fb4c:<path>` fails). The provenance block above promises
the sweep included untracked modules, and it did — the file did not yet exist.
This is the same drift mechanism as row 13: a row describing a corpus that has
since moved. Both modules are on `origin/verified` with the root import
(`git cat-file -e origin/verified:<path>`), so they have passed a real green
`Build and audit`, not merely reached `main`.

### 8--11. Section variables: the advertised property is false

Five declarations sit under an open `variable` they reference, so the
elaborated type has leading inputs that the printed header does not show.

| Declaration | Open `variable` | Site |
|---|---|---|
| `MatricialStabilityRadical.actualCoronaMFResidual_le_fdUnitaryResidual` | `{G : Type u} [Group G]` | `Sofic/MatricialStabilityRadical.lean:35` |
| `MarkedGroupSpace.isClosed_operatorMFLocus` | `{k : ℕ}` | `Sofic/MarkedMFClosed.lean:25` |
| `MarkedGroupSpace.isOpen_compl_operatorMFLocus` | `{k : ℕ}` | same |
| `QuasiRegularWitness.baseVector_apply_base` | `(G : Type u) [Group G] (K : Subgroup G)`, plus `[DecidableEq (G ⧸ K)]` from the inner section | `Analysis/QuasiRegularWitness.lean:29,107` |

No mathematics is at risk: all four are true and unconditional. What is at risk
is the gate's own credibility — it prints "cited declarations are closed" about
declarations that are not. Fix by moving the binders inside the proposition, as
the rest of the badge surface already does, or by adding these names to
`Audit.zeroInputEndpoints` so the elaborated check covers them.

### 12. A badge over a definition

`ManuscriptExactWrappers.ManuscriptHSInvisible` is
`def … : ∀ {H : Type} [Group H], H → Prop`. It defines Hilbert--Schmidt
invisibility; it asserts nothing. `def:invisible` is a definition environment,
so a *link* is appropriate — but `\leanverified` is documented in
`scripts/check_non_mf_refs.py:13` as "an object-level proof of the printed
claim", and there is no claim. Contrast `P13DescentMaster.p13CompletenessEquiv`
and `LiteralBaseCompleteness.baseAffineEquiv`, also `def`s and also badged:
those construct isomorphisms and carry real content, which is why the gate
flags only `Prop`/`Type`-valued definitions.

### 13. Tikuisis--White--Winter, off the badge surface — **RESOLVED 2026-08-17**

**Resolved, and not by supplying the input.** The paragraph was rewritten to
route through models it exhibits rather than through amenability, and badged with
`CliffordBSAmenableMF.manuscriptSharpnessOfKazhdanHypothesis`. The deduction
quoted below is no longer in the manuscript, so the finding this section records
is closed at its manuscript end; the Lean structure survives, unbadged and cited
by nothing, as the formalization of the route the manuscript used to print.

Two corrections to the record, both of which made this look harder than it was.
First, the conclusion never needed the input: the sharpness paragraph concludes
that some homomorphism to `U(Q)` does not kill the mark, and MF-ness of the
realized quotient was only the route chosen to get there. Second, the
unconditional route was already finished and certified while three documents —
this one, the ledger's `CY.13` note, and `NON_MF_LITERATURE_SURFACE` §3.1 — still
described `Sofic/CliffordBSAmenableMF.lean` as uncompiled and outside the import
closure. It is imported at `GroupApproximation.lean:948` and is on
`origin/verified` with that import line, which is proof of a green
`Build and audit`. **Check `git cat-file -e origin/verified:<path>` before
believing a claim in this document that a module does not compile.**

What genuinely remains conditional is narrower than this section states: not the
paragraph, but the single clause `IsOperatorMF RealizedQuotient`, carried as a raw
binder in `Sofic/CliffordBSPrintedRoute.lean:172` and threaded through five
further theorems there. Those are deliberately kept as the formalization of the
printed route. The `AmenableImpliesMF` structure named in this row is a separate
and dead surface — nothing outside its own file mentions it.

`GroupApproximation/Sofic/CliffordBSAmenable.lean:84`

```lean
structure AmenableImpliesMF : Prop where
  mf : ∀ (G : Type) [Group G] [Countable G], IsAmenable G → IsOperatorMF G
```

The brief's `AmenableImpliesMF` example is real and is in this repository. It
is used by exactly two theorems (`isOperatorMF_subgroup_CliffordBS`,
`isOperatorMF_closure_CliffordBS`), neither badged, and nothing else in the
corpus depends on them — the Lean containment is clean.

The manuscript containment is not. The `\paragraph{Sharpness of the Kazhdan
hypothesis.}` block uses
the content in a deduction: "The realized quotient is a subgroup of this
amenable group and is therefore amenable, hence MF by \cite{TWW}." Under rule 4
of the governing standard that is a literature black box in a live inference,
and because the paragraph carries no badge, **no gate in the repository sees
it** — not `check_non_mf_refs.py`, not the zero-input gate, not the new one.
The amenability half is fully machine-checked; only the "hence MF" step is not.

---

## 3. Off-badge watchlist

`--audit-corpus` lists every corpus-defined name that no corpus declaration
ever produces, together with the declarations assuming it: **87 names** today.
Most are ordinary theory parameters (`FDUnitaryRepresentation`,
`UnitVectorSequence`, `Transversal`) whose inhabitation is trivial and simply
never written down; they are vacuity risks at worst and need human triage, not
a gate. The literature-shaped ones, in descending exposure:

| Name | Kind | Assumed by | Stands in for |
|---|---|---|---|
| `DefectRoutingData` | structure | 38 | Hull, strengthened |
| `FournierFacioDefectData` | structure | 22 | Fournier-Facio's HNN skeleton |
| `AdianRabinReduction` | structure | 14 | Rabin 1958 |
| `GroupCStarAdianRabinReductions`, `SubgroupMarkovData` | structures | 12, 3 | the same, for C\*-recognition (`Computability/CStarRecognitionConsequences.lean`) |
| `RoutingLemmaData`, `RelativeCommonQuotientData` | structures | 6, 3 | the bespoke small-cancellation lemma |
| `GreendlingerGate`, `GreendlingerConclusion`, `MetricSmallCancellation` | predicates | 1, 2, 1 | classical `C'(1/6)` Greendlinger |
| `KunThomShulmanDoubleData` | structure | 2 | Kun--Thom / Shulman doubling |
| `MainTheoremData`, `UniversalContainerData`, `SimpleEnvelopeData`, `UniversalFinitelyPresentedKazhdanData`, `TwoConjugacyClassQuotientData` | structures | 2--7 | downstream packaging of the routing lane |
| `IsPointNormMatriciallyStable` | predicate | 3 | Eckhardt--Shulman-style stability |
| ~~`ExistsCyclicConjugate`~~ | predicate | 3 | ~~the classical cyclic-reduction existence lemma for HNN extensions~~ — **discharged**, see row 14 |
| `AmenableImpliesMF` | structure | 2 | Tikuisis--White--Winter |
| `UniversallyActionSofic` | predicate | 1 | Gao, on LERF/LERA groups (`Sofic/AscendingHNNCosetActionSofic.lean:97`) |

None of these is reachable from a badged declaration except through rows 1--7
above; the routing-lane cluster is one connected component hanging off
`FullMFRadicalEndpoint`.

### 3a. `def Foo : Prop` used only as an undischarged hypothesis

This shape deserves naming on its own, because it looks like nothing: it is not
a tagged transcription, it carries no `Data` in its name, and it reads as an
ordinary definition. The gate's `open-predicate` detector is exactly this test —
a corpus `def … : Prop` that no corpus theorem ever concludes, appearing as a
premise the conclusion does not mention. `--audit-corpus` reports **43** such
predicates. Triaged:

* **Literature stand-ins.** ~~`ExistsCyclicConjugate`~~ — **discharged
  2026-08-16; no longer a stand-in.** The diagnosis below was right about the
  gap and wrong about it being unfillable, and is kept for the record:
  it *is* absent from Mathlib at the pinned revision
  (`GroupTheory/HNNExtension.lean` has Britton's lemma and reduced words;
  `GroupTheory/FreeGroup/CyclicallyReduced.lean` covers free groups only), but
  absent-from-Mathlib is not the same as unformalizable. `HNNBrittonCyclic.lean`
  proves it outright from the normal-form theory that *is* there, by absorbing
  the last syllable into the head — a conjugation, so the element's order is
  untouched — and inducting on syllable count, which drops by two per rotation.
  Carried as a hypothesis still at `:177`, `:248`, `:256`, for the import-cycle
  reason in row 14 only.
  The original note continues:
  The module is inside the root import closure (`GroupApproximation.lean:284`)
  so it is compiled and axiom-audited, but its two theorems are terminal:
  nothing consumes them, and no badge reaches them. It is the torsion-free half
  of the same routing lane as rows 3--4, prepared in advance of the
  construction that would use it. Also here: `GreendlingerConclusion`,
  `MetricSmallCancellation`, `GreendlingerGate`, `IsPointNormMatriciallyStable`,
  and `UniversallyActionSofic` (whose docstring cites Gao).
* **Transport subject matter, correctly exempt.** `IsScaledAsymptoticCommutant`,
  `IsScaledAsymptoticIntertwinerOf`, `NaturalHSCommutatorVanishing`,
  `NaturalHSIntertwinerVanishing`, `IsAsymptoticIntertwiner`, `HSDistVanishing`.
  The conclusion is the same predicate at a transformed argument.
* **Ordinary definitions and theory parameters**, undischarged only because no
  one had reason to exhibit an instance: `IsInvariant`, `IsNormBoundedOn`,
  `HasTaggedExpansionAtScale`, `HasWindowedAuxiliaryWitness`,
  `HasNoNontrivialMixedQuotient`, `IsQuasiCocycle`, `IsInvolutiveCompressionWitness`,
  `IsPurelyMatricialField`, `IsPPF`, `IsPFF`, `IsTracePMF`, and the
  `Domination/*` character-domination family. Vacuity risks at worst.
* **Known false positive.** `HasCheegerLowerBound` is concluded by
  `KunSpectral.no_uniform_spectral_gap`, but inside `∃ m, 4 ≤ m ∧ (switched m).HasCheegerLowerBound 1 ∧ …`
  — a conjunct under an `∃`, reached by dot notation, which the producer scan
  does not parse. Listed here rather than silently filtered.

---

## 4. Reviewed and cleared

Recorded so that a later reader does not re-litigate them. Each looked
conditional and is not.

* **`ProperProjectionCompression.isometry_not_isUnit` / `not_isStablyFiniteRing`
  / `no_faithfulTracialState`** (badged). Premise is a
  `ProperProjectionCompression`, built by
  `MaximalCStarProperCompression.toProperProjectionCompression` from a
  `StrictKazhdanCompression`, which
  `ChosenMaximalCStarInfinite.nonempty_strictCompression`
  (`Sofic/ChosenMaximalCStarInfinite.lean:74`) constructs unconditionally for
  the chosen group. Discharged, transitively, from nothing.
* **`FinitePresentationSemantics`**: discharged by
  `PresentationCodes.semantics`.
* **`NormModel.exists_hs_collapse`**, **`ScaledKazhdanTransport.scaled_transport_both`**,
  **`IntertwinerKazhdanTransport.*`**, **`TensorPowerTransport.manuscriptFixedTensorTransport`**,
  **`KazhdanAsymptoticCommutant.manuscriptKazhdanTransport`**. Their premises
  (`NormModel`, `IsScaledAsymptoticCommutant`, `NaturalHSCommutatorVanishing`, …)
  are the theorems' *subject matter*: the conclusion is the same predicate at a
  transformed argument. "If `x` is an asymptotic commutant then so is `uxu*`"
  says something whether or not commutants exist. The gate exempts a premise
  the conclusion mentions, for this reason.
* **`ManuscriptExactWrappers.manuscriptAbstractNormalKazhdanObstruction`**. Its
  `hDkill` hypothesis abstracts the tracial-vanishing property of the defect;
  the concrete instance `manuscriptNormalKazhdanObstruction` discharges it.
* **`TorsionSpectralCollapse.actualCoronaMFResidual_eq_torsionCollapseDefect_of_kazhdan`**.
  The premise `IsCDEOperatorMF (E ⧸ …)` is a genuine hypothesis about a
  specific quotient, printed as such; `IsCDEOperatorMF` is proved for groups in
  the corpus.
* **`KazhdanCompressionCore.manuscriptCentralSignCriterion`** and
  **`KazhdanCliffordConstruction.kazhdanCliffordConstruction`**, whose types are
  the bare names `ManuscriptCentralSignCriterion` and
  `KazhdanCliffordConstructionStatement`. Unfolding both named `Prop`s (the
  gate does this, up to depth 3) shows only benign premises: property `(T)`,
  injectivity, compression, all discharged in the corpus. This is the disguise
  the brief warned about — hypotheses one indirection away, inside a named
  `Prop` — and in these two cases it is clean.
* **`LiteralTietzePresentation.manuscriptTietzeSixGeneratorPresentation`** opens
  with a vestigial `∀ _ : Unit`. Harmless, but it is noise in a statement whose
  whole purpose is to be read.

---

## 5. The gate: `scripts/check_non_mf_unconditional.py`

Same CLI shape, output style and exit-code discipline as its siblings:
`--root`, `--tex`, `--self-test`, problems to stderr under a
`check-non-mf-unconditional: N problem(s):` header, exit 1 on any finding,
exit 0 with a one-line count otherwise. Plus `--explain` (per-badge verdict,
always exit 0) and `--audit-corpus` (the § 3 watchlist, always exit 0).

**What counts as a premise:** a header binder, an in-scope `variable` the
statement references and does not shadow, a binder in the statement's leading
`∀`-telescope, or a top-level `→` antecedent — and the same, one indirection
down, inside any named corpus `Prop` the statement reduces to.

**What makes a premise conditional:** its type head is a name *this repository*
defines (`structure`, `class`, `inductive`, or `def … : Prop` — Mathlib and
core names are never findings, per the governing standard's one permitted
base), the corpus never discharges it, and the conclusion never mentions it.
Discharge is a least fixed point over producers: a producer discharges its
result only when its own premises are discharged, which is what separates
`DefectRoutingData` (open) from `ProperProjectionCompression` (closed).

**Detectors:** `header-binder`, `open-variable`, `conditional-data`,
`open-predicate`, `literature-input` (roster), `known-conditional` (in-script
pin), `definition-only`. Each is calibrated by a planted positive *and* a
planted negative in `--self-test`, in the style of
`scripts/Audit/Plants.lean`.

**Rosters.** `KNOWN_CONDITIONAL_DECLARATIONS` lives in the script, not in a
data file, for the reason `Audit.literatureInputNames` does: the corpus must
not be able to untag its own citations. A pinned name that is no longer cited
is reported as stale, so the roster cannot outlive the problem it records. The
file roster `--literature-roster notes/NON_MF_LITERATURE_INPUTS.txt` (absent,
hence empty, mirroring `Audit.literatureInputNames`) is the secondary
mechanism, for transcriptions the structural rule cannot see.

**Blind spots**, all of which can only hide a finding, never invent one:

* premise walking stops at a `let`/`letI`/`haveI` in the statement spine;
* named-`Prop` unfolding stops at depth 3 and does not follow `abbrev` chains
  through Mathlib;
* a premise that is a bare logical formula is judged by the head symbols it
  mentions, not by whether the formula is provable — this is why rows 2 and 5
  needed hand pins;
* `variable` tracking is textual: a `variable` the elaborator includes through
  a dependency the statement does not name is missed;
* it is a lexical scan, like every checker in `scripts/`. The semantic version
  of the header check already exists (`Audit.hasLeadingInput`); the semantic
  version of *this* check would be an environment scan over premise types,
  which belongs in `scripts/Audit/Scan.lean` and would subsume the whole
  script.

---

## 6. Proposed rename: `zero-input` → `source-closed`

The existing gate checks a real and useful property. The problem is only its
name, which reads as unconditionality and is being cited as unconditionality.
Proposed term: **source-closed** — the declaration's *source text* is closed;
its mathematics may not be. (`closed-header` is the alternative and says the
same; `source-closed` is preferred because it names what is actually inspected,
and makes the gap to the elaborated type audible.)

I do not own `scripts/check_non_mf_zero_input.py` and have not edited it.
Exact edits, if the rename is adopted:

**`scripts/check_non_mf_zero_input.py`** (file rename to
`check_non_mf_source_closed.py` optional; the strings matter more)

| Line | Now | Proposed |
|---|---|---|
| 2 | `"""Require every Lean declaration cited by the non-MF paper to be zero-input.` | `"""Require every Lean declaration cited by the non-MF paper to be source-closed.` |
| 6-14 | docstring body: "makes the closed status of a manuscript endpoint visible and mechanically auditable" | add: source-closure is a property of the printed header only; it does not inspect section `variable`s and says nothing about what the proposition assumes — see `check_non_mf_unconditional.py` |
| 37 | `def declaration_is_zero_input(source, short_name) -> bool:` | `def declaration_is_source_closed(source, short_name) -> bool:` |
| 69 | `closed = declaration_is_zero_input(` | `closed = declaration_is_source_closed(` |
| 79-80 | `f"line {line_number}: {declaration} has declaration inputs; move every binder after the colon"` | unchanged (accurate as written) |
| 84 | `print(f"check-non-mf-zero-input: {len(problems)} problem(s):")` | `check-non-mf-source-closed:` |
| 89 | `print(f"check-non-mf-zero-input: {checked} cited declarations are closed")` | `check-non-mf-source-closed: {checked} cited declarations are source-closed` — the key line, since this is the string being read as an unconditionality claim |

**Call sites** (path only changes if the file is renamed; the log strings above
change regardless):

* `.github/workflows/prover.yml:423` and `:740`
* `.github/workflows/build-non-mf-pdf.yml:154`

**Prose**

* `README.md:304-306` — "enforces that every Lean declaration cited by the
  non-MF manuscript has no declaration inputs (all quantifiers occur inside the
  proposition)" is accurate; add that this is a source-text property and name
  the unconditionality gate alongside it.
* `README.md:136` — "joined by the zero-input declarations" → "source-closed".
* `scripts/lean_decls.py:41` and `scripts/claim_map.py:40` mention the script by
  filename only; update if the file is renamed.
* `scripts/Audit.lean:603-622` uses the same vocabulary for a *semantic* check
  (`zeroInputEndpoints`, "Advertised closed endpoints"). That one earns the
  stronger word for the fifteen names on it, but "zero-input" there means the
  same narrow thing — no leading `forallE` — and the docstring should say so.

---

## 7. Remediation, in the order that buys the most

1. **Restate the badges that the prose already admits are conditional.**
   `\leanconditional` exists, is documented (`check_non_mf_refs.py:9-17`), is
   checked, and is used **zero** times in the manuscript. Rows 1--5 are
   described in the surrounding prose as conditional; only the macro disagrees.
   Five badge edits, no Lean, no mathematics — and the largest single
   improvement in the honesty of the badge surface.
2. **Point the `LITERATURE_INPUT` gate at what the corpus actually does.** The
   roster takes `Name`s of tagged `Prop`s; the corpus's literature inputs are
   structures. Either add named `Prop` aliases for `AdianRabinReduction`,
   `DefectRoutingData`, `AmenableImpliesMF` and put them on
   `literatureInputNames`, or extend `Audit.literatureScan` to accept structure
   names. Until one of the two happens, an empty roster reads like a clean bill
   of health.
3. ~~**Badge the sharpness paragraph, or drop the deduction.**~~ **DONE
   2026-08-17, and better than either option.** The recommendation was to make the
   TWW dependency auditable with a `\leanconditional`; instead the deduction was
   dropped and the paragraph badged `\leanverified` over
   `CliffordBSAmenableMF.manuscriptSharpnessOfKazhdanHypothesis`, so there is no
   dependency left to audit. See §13.
4. **Move four binder groups inside their propositions** (rows 8--11), or add
   those names to `Audit.zeroInputEndpoints`. Mechanical.
5. **Decide `def:invisible`** (row 12): keep the link but at a status that does
   not claim a proof.
6. **Wire the new gate into CI report-only first**, next to
   `check_non_mf_zero_input.py` in `prover.yml` and `build-non-mf-pdf.yml`. It
   exits 1 today by design; the doctrine in `scripts/Audit.lean:684-690` is that
   there are no budgets and no ratchets, so it should not become a required gate
   until items 1--5 land, at which point it should be required and stay at zero.
