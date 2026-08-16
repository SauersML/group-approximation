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
run: **88 unconditional, 12 conditional** (15 findings, rows 1--12), no badge
carrying any of the other five certification statuses. Rows 13--14 are off the
badge surface. By category, over *declarations*:

| Category | Count | Rows |
|---|---|---|
| unconditional | 88 | — |
| conditional-data — undischarged existence package | 3 | 1, 3, 4 |
| literature-input — published theorem as a quantified premise | 2 | 2, 5 |
| open — corpus predicate no corpus theorem concludes | 2 | 6, 7 |
| *(not mathematical conditionality)* header-hygiene | 4 | 8--11 |
| *(not mathematical conditionality)* category error | 1 | 12 |

So **7 of 100 badged declarations are mathematically conditional**, and 5 more
carry a badge defect that is not conditionality. Reproduce with

```
python3 scripts/check_non_mf_unconditional.py --explain      # per-badge verdict
python3 scripts/check_non_mf_unconditional.py --audit-corpus # off-badge watchlist
python3 scripts/check_non_mf_unconditional.py                # the gate (exit 1 today)
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
| 1 | `MarkovMFConsequences.operatorMF_recognition_undecidable` | literature-input | § "Undecidability of MF recognition", prose after `\end{corollary}` of `cor:undecidable` | **Total.** The printed corollary is unconditional; its only Lean support is conditional. | `Computability/AdianRabinMarkovProperty.lean` — certifies the *hypotheses* of Adian--Rabin, explicitly not the theorem |
| 2 | `ContinuumMultiplicity.manuscriptContinuumMultiplicity` | literature-input | § "Undecidability of MF recognition", multiplicity paragraph citing `\cite{Neumann37}` | **Total** for the `2^{ℵ₀}` sentence; the `E × ℤ^k` sentence is unaffected. | `Sofic/ContinuumFamilyCriterion.lean` (already committed) shrinks the obligation to one construction; no new module supplies it |
| 3 | `FullMFRadicalEndpoint.exists_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical` | conditional-data | § "Questions", torsion-free f.p. non-MF group | **Total** for that answer. Prose already says "neither is an unconditional statement". | `Monsters/FournierFacioRealization.lean`, `Monsters/RealizationEmbedding.lean`; scope now fixed by `docs/HULL_ROUTING_AUDIT_2026-08-16.md` |
| 4 | `FullMFRadicalEndpoint.exists_group_with_every_nontrivial_quotient_not_isCDEOperatorMF` | conditional-data | same | as above | same |

Rows 3–4 were audited against the literature on 2026-08-16
(`docs/HULL_ROUTING_AUDIT_2026-08-16.md`, read from Hull, *Small cancellation
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
| 5 | `ClosedEnvelopeCompression.manuscriptEnvelopeCompressionBlind` | literature-input | `rem:chaincondition`, Zariski-envelope sentence | **Total** for the algebraic-envelope sentence; the tensor-rigidity badge beside it is unaffected. | `Algebra/ZariskiClosedSubgroup.lean`; the `Algebra/ZariskiDescendingChain` it cites **does not exist yet** |
| 6 | `MatricialStabilityRadical.actualCoronaMFResidual_eq_fdUnitaryResidual` | open-predicate | `prop:stabradical` clause 2 | Clause 2 is *printed* conditional, so no print/Lean mismatch — but the hypothesis is satisfied by no group in the corpus, so the clause is never applied. | none seen |
| 7 | `MatricialStabilityRadical.not_isCDEOperatorMF_of_stable_of_fdResidual_ne_bot` | open-predicate | `prop:stabradical` clause 3 | as above | none seen |
| 8 | `MatricialStabilityRadical.actualCoronaMFResidual_le_fdUnitaryResidual` | header-hygiene | `prop:stabradical` clause 1 | None mathematically; the theorem is true and unconditional. | — |
| 9 | `MarkedGroupSpace.isClosed_operatorMFLocus` | header-hygiene | `thm:markedclosed`(1) | None mathematically. | — |
| 10 | `MarkedGroupSpace.isOpen_compl_operatorMFLocus` | header-hygiene | `thm:markedclosed`(2) | None mathematically. | — |
| 11 | `QuasiRegularWitness.baseVector_apply_base` | header-hygiene | `rem:maxinfinite` | None mathematically. | `Analysis/ResiduallyFiniteDimensional.lean` works on the same remark (different clause) |
| 12 | `ManuscriptExactWrappers.ManuscriptHSInvisible` | category | `def:invisible` | None; but the badge certifies a definition, not a claim. | — |
| 13 | `CliffordBSAmenable.isOperatorMF_subgroup_CliffordBS` | literature-input, **off-badge** | `\paragraph{Sharpness of the Kazhdan hypothesis.}` | **Total** for the sharpness paragraph's key step. Carries no badge, so no gate sees it. | `Algebra/AmenableMFProof.lean`, `Analysis/AmenableQuasidiagonal.lean` — both analyse what the step costs; neither supplies it |
| 14 | ~~`HNNTorsionFree.isPowerTorsionFree_of_existsCyclicConjugate` (and `…_sourceGroup_…`, `…_integerSourceGroup_…`)~~ | ~~literature-input~~ → **CLOSED 2026-08-16** | none — no manuscript claim cites it yet | **None.** `ExistsCyclicConjugate` is now proved, not assumed: `HNNBritton.existsCyclicConjugate` (`GroupTheory/HNNBrittonCyclic.lean`, commit `ae4053f7`) discharges it for every `φ` from Mathlib's HNN normal-form theory. The three hypothesis-taking theorems remain only because that file imports `Algebra/HNNTorsionFree.lean` (invoking it there would be an import cycle); they are superseded one for one by `HNNBritton.isPowerTorsionFree_hnn`, `…_sourceGroup`, `…_integerSourceGroup`. | — |
| 15 | ~~`NuclearityAmenability.not_isAmenable_of_base_embeds`~~ | ~~header-hygiene~~ → **CLOSED 2026-08-16** | `thm:D`, the non-nuclearity paragraph | **None.** The manuscript now badges the wrapper `manuscriptNotAmenableOfBaseEmbeds`, whose binders are all after the colon, so the finding is gone rather than accepted. | — |
| 16 | ~~`SoficByAmenablePermanence.isSofic_of_isSofic_ker_of_isAmenable`~~ | ~~header-hygiene~~ → **CLOSED 2026-08-16** | `\paragraph{Extensions by $\Z$.}` | **None.** Superseded by the badged wrapper `manuscriptSoficOfSoficKerOfAmenableQuotient`. | — |
| 17 | ~~`ZariskiClosedSubgroup.manuscriptZariskiClosureOfRepresentation`~~ | ~~header-hygiene, open-variable~~ → **CLOSED 2026-08-16** | `rem:chaincondition` | **None.** Superseded by `manuscriptZariskiRepresentationEnvelopeClosed`, which binds `n`, `k` and the field instances after the colon, so the open-variable half is closed too.  Row 5 on the same remark is a genuine literature input and stays. | — |
| 18 | `MarkovMFConsequences.presentationCodes_recognition_undecidable_of_haltingReduction`, `…_negative_side_not_re_of_haltingReduction` | conditional-data, buried-conditional | `cor:undecidable`, the two badges under the corollary | **None for the print/Lean relation, which is the thing this document audits.** Row 1's reduction is here an *explicit hypothesis*, and `cor:undecidable` is printed conditional in as many words — "suppose given a computable map sending each instance of the halting problem to a presentation code whose group is MF exactly when that instance halts". Badge and printed statement therefore have the same strength. What collapses if the reduction is never built is the *unconditional* undecidability of MF recognition, which row 1 already tracks and which the manuscript does not claim. The `buried-conditional` half names `haltingProperty` under the same premise; that is the halting problem, named, not a second input. | `Computability/AdianRabinMarkovProperty.lean` and `Computability/HaltingReduction.lean` — the first certifies the Markov hypotheses, the second the reduction interface; neither constructs an `AdianRabinReduction` |
| 19 | ~~`kt_06_ultraproduct_finite`, `kt_10_finiteness_reverses`~~ | ~~header-hygiene~~ → **CLOSED 2026-08-16** | `lem:ultrafinite`, `lem:finitecompare` | **None mathematically**, and now nothing to accept: both are fixed in place by the rows 8--11 method, binders after the colon and a leading `intro`. These two badges arrived with the Step 6 rewrite of `thm:collapse` and were never on the baseline. `kt_10` had no section variables at all; `kt_06` draws `(Z : ℕ → FiniteModel)` and `[∀ n, Nonempty (Z n)]` from the `Polar` section block, and they are restated in that order, so the elaborated type does not move. | — |

### Status, 2026-08-16: rows 8--12 and the gate

The sweep above is a snapshot and is left as recorded.  What has moved since:

| # | Now | Where |
|---|---|---|
| 8 | **fixed.** `∀ {G : Type u} [Group G], …` inside the proposition; proof unchanged apart from a leading `intro G _` | `Sofic/MatricialStabilityRadical.lean` |
| 9 | **fixed.** `∀ {k : ℕ}, …`; proof unchanged apart from `intro k` | `Sofic/MarkedMFClosed.lean` |
| 10 | **fixed.** likewise, and its one-line proof now names the rank explicitly | same |
| 11 | **fixed.** `∀ (G : Type u) [Group G] (K : Subgroup G) [DecidableEq (G ⧸ K)], …`; same elaborated type as before, now printed | `Analysis/QuasiRegularWitness.lean` |
| 12 | **Lean side landed, badge move pending.** `ManuscriptExactWrappers.manuscriptHSInvisibleCharacterization` states what a badge on `def:invisible` can honestly certify: fidelity of the predicate to the printed text, the identity of that predicate with the `hDkill` premise of `thm:abstract-nk`, and that invisibility is a subgroup condition. The badge and `CLAIM_TARGETS["def:invisible"]` still point at the definition | `Sofic/ManuscriptExactWrappers.lean` |

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
`docs/NON_MF_UNCONDITIONAL_BASELINE.txt`, an itemized register of the findings
this document records.  A finding not on it fails; an entry that matches
nothing fails too, so a discharged row cannot leave its exemption behind.
There is no count in the mechanism and `--strict` ignores the register
entirely, which is the end state once rows 1--7 land.

### Cross-check against the manuscript's own prose

Grepping the `.tex` for self-declared conditionality (`quantifies over`,
`not formalized`, `literature input`, `as a hypothesis`, `conditionally on`,
`not an unconditional`) returns exactly **four** sites, and all four are rows
above: `rem:chaincondition` (row 5), the `cor:undecidable` discussion (row 1),
the Neumann paragraph (row 2), the `\subsection{Questions}` routing datum
(rows 3--4). A fifth hit, at `def:radical` — "that is the form the
formalization quantifies over" — is benign: it names the definitional variant,
and the equivalence is itself proved (`prop:mf-equivalences`).

The manuscript, in other words, already knows about four of these and says so
in print. In all four cases the sentence admitting the condition sits within a
few lines of a `\leanverified` badge.

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

No corpus-defined name appears here, so the structural rule cannot see it; it
is pinned by hand in `KNOWN_CONDITIONAL_DECLARATIONS`
(`scripts/check_non_mf_unconditional.py`). The premises jointly *are* Neumann
1937, and the corpus never exhibits such a family. The module docstring is
explicit: "The existence of such a continuum family is B. H. Neumann's, and it
is not proved here: it enters as a hypothesis."

What is genuinely proved on top of it is the manuscript's own counting step
(countable groups have countably many f.g. subgroups, so the fibres are
countable) — real content, and the honest badge for it is `\leanpartial` or
`\leanconditional`, not `\leanverified`.

### 3--4. The routing datum

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

Same shape as row 2 and invisible to the same rule: every premise is in
Mathlib vocabulary (`Subgroup … → Prop`, `WellFoundedLT`), so no corpus-defined
name appears and the structural test has nothing to bite on. It is pinned by
hand in `KNOWN_CONDITIONAL_DECLARATIONS`.

The two premises jointly *are* the classical theorem that Zariski closed
subgroups of `GL(V)` satisfy the descending chain condition, and the corpus
exhibits no `Closed` for which the instance holds. `rem:chaincondition` says
this in as many words — "That the closed subgroups of `GL(V)` in the Zariski
topology satisfy the chain condition is classical, and is the input the badge
quantifies over rather than proves" — one line below the badge.

What *is* proved is the poset deduction: a conjugation-equivariant monotone
envelope landing in a well-founded family is fixed by one-sided compression.
Real content, and correctly badged as `\leanconditional` rather than
`\leanverified`.

A peer session is writing `Algebra/ZariskiClosedSubgroup.lean` against exactly
this gap. Its docstring defers the chain condition itself to
`Algebra/ZariskiDescendingChain`, which does not exist at this revision, so the
item is open and in progress.

### 6--7. Point-norm matricial stability

`GroupApproximation/Sofic/MatricialStabilityRadical.lean:175` and `:186`,
premise `IsPointNormMatriciallyStable G` (defined at `:40`). No corpus theorem
concludes it for any group.

This one is different in kind from 1--5 and should not be lumped with them.
`prop:stabradical` prints clauses 2 and 3 *with* the stability hypothesis, so
Lean and print agree exactly; the honest reading is a printed hypothesis, not a
smuggled literature import. The residual concern is vacuity: with no group
proved stable in the corpus, and the intended witnesses (Eckhardt--Shulman,
Dadarlat-style stability results) unformalized, clauses 2--3 are never applied
to anything. The gate reports them because the user's standard is that a
premise the corpus cannot satisfy is a premise the corpus has not discharged.
Whether that warrants a badge change is a judgement call for the manuscript
owner; the mechanical answer is recorded here either way.

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

### 13. Tikuisis--White--Winter, off the badge surface

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
file roster `--literature-roster docs/NON_MF_LITERATURE_INPUTS.txt` (absent,
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
3. **Badge the sharpness paragraph, or drop the deduction.** Row 13 is invisible
   to every gate precisely because it has no badge. A `\leanconditional` over
   `isOperatorMF_subgroup_CliffordBS` would make the TWW dependency auditable
   instead of leaving it as the one live literature inference no tool can see.
4. **Move four binder groups inside their propositions** (rows 8--11), or add
   those names to `Audit.zeroInputEndpoints`. Mechanical.
5. **Decide `def:invisible`** (row 12): keep the link but at a status that does
   not claim a proof.
6. **Wire the new gate into CI report-only first**, next to
   `check_non_mf_zero_input.py` in `prover.yml` and `build-non-mf-pdf.yml`. It
   exits 1 today by design; the doctrine in `scripts/Audit.lean:684-690` is that
   there are no budgets and no ratchets, so it should not become a required gate
   until items 1--5 land, at which point it should be required and stay at zero.
