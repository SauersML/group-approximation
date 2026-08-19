# Transitive proof-dependency trace of the non-MF manuscript badges

Snapshot: working tree at `be0ecb1e` plus uncommitted teammate edits,
`non_mf_groups_exist.tex` at 4011 lines, **100** `\leanverified` badges,
19 019 declarations indexed, **3 038** distinct declarations inside the union of
the 100 badge closures.  Several of the paths described here are being rewritten
by other sessions *right now*; every such item is marked **IN FLIGHT** with the
agent that owns it.  Re-run the tool before acting on any single line.

TeX line numbers quoted below drift as teammates edit the manuscript — the file
grew from 3836 to 4011 lines during this analysis, and
`manuscriptRadicalPortability`'s badge moved from line 2229 to line 2740 in that
time.  Declaration names and `Module.lean:line` references are the stable
identifiers; treat the tex line numbers as approximate locators.

## What question this document answers

The other manuscript gates ask about the badged declaration itself:

| gate | question |
| --- | --- |
| `scripts/check_non_mf_refs.py` | does the cited declaration exist? |
| `scripts/check_non_mf_zero_input.py` | is its header closed at the colon? |
| `scripts/check_non_mf_unconditional.py` | are *its own* premises dischargeable? |

None of them looks past the badge.  The standard the manuscript is held to does:

> It is not enough for a manuscript-facing theorem's top-level proof to resemble
> the TeX.  Every helper it invokes must be checked against the corresponding TeX
> step.  If a helper contains a mathematically different proof of something whose
> proof is specified in the manuscript, that helper must be replaced on the
> manuscript path.

So a badged theorem can have a faithful three-line top-level proof and still be a
MISMATCH four levels down.  This document is the transitive-helper dimension of
the audit, and only that dimension.  It deliberately does not duplicate:

* the step-level TeX claim ledger (`ledger`) — which TeX steps exist at all;
* the conditional-hypothesis catalogue (`conditional-sweep`) — which premises are
  open.  Where a conditional appears **in a closure** rather than in a badge
  header, it is reported here and cross-referenced there;
* the per-theorem step audits (`p13-stepaudit`, `collapse-stepaudit`).

The four questions asked of every helper in every closure:

* **(a) different route** — the helper proves something the manuscript also
  specifies a proof for, but by a different argument;
* **(b) stronger theorem** — a general theorem discharges a step the manuscript
  proves concretely;
* **(c) foreign abstraction** — the conclusion is reached through a layer the
  manuscript does not use;
* **(d) conditional in the closure** — an open hypothesis or literature-input tag
  anywhere below the badge.

Four flags implement these.  `conditional` reports a corpus-defined,
never-discharged package **in head position** of a premise, and agrees with
`check_non_mf_unconditional.py` by construction.  `buried` reports the same kind
of package appearing *anywhere inside* a premise type — the bundling-structure
class, where

```lean
(ambient : ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
   UltraproductAdjointModel iota s d U ω)
```

has head `Ultrafilter`, so head-only detection reports nothing while the premise
is exactly as unconstructible as one in head position.  Read `buried` as a lead
and `conditional` as a verdict.  `literature` is the roster test and
`abstraction` the foreign-layer name test.

## The tool

`scripts/trace_manuscript_deps.py`.  Source-level: it never invokes `lake`,
`lean` or `#print axioms`.  It parses `.lean` text, tracks the
`namespace`/`section`/`open` stack, resolves the `import` graph, extracts the
identifiers each declaration mentions, and walks the closure breadth-first.

```
scripts/trace_manuscript_deps.py --summary            # one line per badge
scripts/trace_manuscript_deps.py --decl NAME          # spanning tree of one badge
scripts/trace_manuscript_deps.py --flagged-only       # findings with shortest paths
scripts/trace_manuscript_deps.py --shared 30          # helpers on >= 30 paths
scripts/trace_manuscript_deps.py --forward-refs       # badges reaching later badges
scripts/trace_manuscript_deps.py --format json|dot
scripts/trace_manuscript_deps.py --check              # gate: closure conditionals fail
scripts/trace_manuscript_deps.py --self-test
```

It reuses `scripts/lean_decls.py` (comment stripping, modifier grammar) and
`scripts/check_non_mf_unconditional.py` (binder parsing, the corpus-defined /
never-discharged fixed point), so the conditionality verdicts here and in that
gate agree by construction; the only difference is that the gate applies the test
to badges and this applies it to everything they reach.

### Accuracy, honestly

The analyser **over-reports**.  Every scope prefix that could resolve a token
contributes an edge, not just the one Lean would pick; a token that resolves
nowhere in scope falls back to a suffix match on its last component; statements
are scanned as well as proofs.  Consequences you will see in the output:

* Edges marked `~` are **heuristic**.  They recover dot-notation (`hx.comap`) and
  `export`ed names, at the cost of firing on every declaration in the import
  closure that shares that final component.  `IsOperatorMF.subgroup` shows six
  `…​.comap` children where only `IsOperatorMF.comap` is real.
* The two badge statements that appear to mention `WeakMFApproximation.comap`
  (`manuscriptRadicalReductionToQuotient`, `manuscriptRelationClosure`) are this
  false positive on `Subgroup.comap`.  **No badge statement mentions the
  universal-ultraproduct layer** — see finding T1.
* Local hypotheses named like repository lemmas produce edges.
* Mathlib and core names are absent from the index by construction, so they never
  appear.  Mathlib is the permitted base, not a dependency to audit.
* 76 of the 100 closures hit the default depth cap of 6 and are marked
  `TRUNCATED`.  Findings below depth 6 exist and are not in this document.

Two badges have **zero** repository helpers, and that is correct rather than a
scanner failure — both are pure Mathlib arguments:
`commutator_conjugate_eq_commutator_sq_of_sq_eq_one`
(`Sofic/CompressionDefectSquare.lean:30`) and
`finiteSubgroup_eq_bot_of_isMulTorsionFree`
(`Sofic/TorsionFreeFiniteNormalLimit.lean:19`).

The corpus contains **0** `sorry`, `axiom`, and `native_decide`.

---

# Findings, ranked by centrality of the affected manuscript claim

## T1 — The five-rung MF-radical ladder, and the one rung that is not a manuscript object

**Category (c), plus an objects question.  Reach: the widest of any finding —
Definition `def:radical`, Proposition `prop:mf-equivalences`, Proposition
`prop:univquot`, Theorem `thm:criterion`, Theorem `thm:normal-kazhdan`, Theorem
`thm:abstract-nk`, Corollary `cor:intrinsic-nk`, Theorem
`thm:compression-radical`, Lemma `lem:permanence`, Proposition
`prop:stabradical`, Theorems A and D, and the whole collapse section.**

The manuscript has exactly one MF radical (Definition, tex:2226):

> Rad_MF(G₁) = ⋂ { ker Θ : Θ a corona representation of G₁ }

with one corona, the sequential `∏ₙ M_{dₙ}(ℂ) / ⊕ₙ M_{dₙ}(ℂ)` of
eq:corona, and it records that arbitrary positive dimensions and strictly
increasing ones give the same intersection.  The Lean development has six
`Subgroup`-valued residuals:

| declaration | quantifies over | manuscript object? |
| --- | --- | --- |
| `manuscriptCoronaMFResidual` (`Sofic/ActualCoronaMFRadical.lean:76`) | `d : ℕ → ℕ` positive, target `unitary (NormMatrixCStarCorona (naturalFiniteModel ∘ d))` | yes — the printed one |
| `cdeMFResidual` (`Sofic/CDEMFRadical.lean:30`) | same, plus `StrictMono` dimensions | yes — the strictly increasing convention |
| `actualCoronaMFResidual` (`Sofic/ActualCoronaMFRadical.lean:41`) | abstract `FiniteModel` coordinates instead of `Fin dₙ` | yes, re-coordinatized |
| `coronaMFResidual` (`Sofic/NormMFCoronaRadical.lean:32`) | target `NormMatrixCoronaUnitary` (the `U_cor` of eq:unitary-corona) | yes, via κ of eq:unitary-corona-iso |
| `fdUnitaryResidual` (`Sofic/MatricialStabilityRadical.lean:49`) | finite-dimensional unitary reps | yes — `Rad_fd` of prop:stabradical |
| **`normMFResidual`** (`Sofic/NormMFResidualDetector.lean:70`) | **every index type `I`, every ultrafilter `U` on `I`, principal ones included**, target `UniversalWeakMF U X` | **no** |

`normMFResidual` is defined through `NormMFInvisible`:

```lean
def NormMFInvisible (x : G) : Prop :=
  ∀ (I : Type) (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X), rho x = 1
```

and its own docstring says so: *"The historical name `normMFResidual` is not a
definitional identification with the paper's cofinite-corona radical."*

The manuscript does use the words.  In the appendix proof of
`prop:mf-equivalences` (tex:3527–3536) it writes *"make the group weakly MF"* and
*"Weak MF in turn makes the norm-MF radical of Definition~\ref{def:radical}
trivial"* — but it explicitly identifies that radical with `def:radical`, one
sequential corona.  It never introduces an arbitrary-index, arbitrary-ultrafilter
object.

**What is fine.**  The comparison theorems are proved, not assumed:
`coronaMFResidual_eq_normMFResidual` for countable groups
(`Sofic/NormMFCoronaRadical.lean:83`), through
`NormMFInvisible.toCoronaMFInvisible` and `CoronaMFInvisible.toNormMFInvisible`.
And no badged **statement** mentions the foreign layer: the printed objects are
the ones in the printed propositions.  `manuscriptMFRadical` uses
`manuscriptCoronaMFResidual` and nothing else (7 helpers, 0 flags) — the
definition badge is exact.

**What is not fine.**  Almost every manuscript-facing *proof* in the radical and
obstruction half of the paper descends to the foreign rung and climbs back:

```
manuscriptFiniteNormalObstructionCriterion            (thm:criterion)
  -> finiteNormal_le_normMatrixCStarCoronaKernel
    -> finiteNormal_le_normMatrixCoronaKernel
      -> KazhdanCompressionCore.finiteNormal_le_normMFResidual
        -> finiteNormal_le_normMFResidual_of_hyperlinear_killed
      -> NormMFInvisible.toCoronaMFInvisible

manuscriptUniversalMFQuotient                         (prop:univquot)
  -> exists_manuscriptCoronaRepresentation_ker_eq_manuscriptCoronaMFResidual
    -> exists_actualCoronaRepresentation_ker_eq_actualCoronaMFResidual
      -> exists_normMatrixCoronaRepresentation_ker_eq_coronaMFResidual
        -> coronaMFResidual_eq_normMFResidual
        -> exists_normMatrixCoronaRepresentation_ker_eq_normMFResidual
```

Badges whose closure reaches the foreign rung (abstraction count from
`--summary`, at this snapshot): `manuscriptIntrinsicNormalKazhdanRadical` 20,
`manuscriptIntrinsicNormalKazhdanPart` 19, `manuscriptNormalKazhdanObstruction`
18, `manuscriptAbstractNormalKazhdanObstruction` 18,
`literalWitness_locallyFiniteKernel_nonMF` 18, `isOperatorMF_of_residuallyFinite`
16, `isOperatorMF_of_locallyFinite` 16, `manuscriptCompressionRadical` 16,
`literalWitness_LEFKernel_integerExtension_nonMF` 16,
`exists_twoGenerated_…_fullMFRadical` 14, `manuscriptQuotientNonclosure` 13,
`manuscriptUniversalMFQuotient` 13, `manuscriptRelationClosure` 12,
`actualCoronaMFResidual_eq_torsionCollapseDefect_of_kazhdan` 12,
`manuscriptMFDefinitionEquivalences` 11,
`manuscriptFiniteNormalObstructionCriterion` 11, `manuscriptTheoremA` 11,
`manuscriptTheoremFamily` 11, `manuscriptCollapseRadicalReduction` 11.

**The concrete cost, not just an aesthetic one.**  Because the foreign rung
quantifies over arbitrary ultrafilters, `isOperatorMF_of_normMFResidual_eq_bot`
(`Sofic/NormMFUniversalCorona.lean:348`) must first convert arbitrary-ultraproduct
detectors into sequential ones (`hdetect` produces an unknown `I` and `U` per
element) before it can run the block-sum diagonalization.  The manuscript's
version of the same step (appendix, "the block-sum diagonalization in the proof of
Proposition~\ref{prop:univquot}(2) then assembles the detecting sequences") starts
from sequential models and needs no such conversion.  That conversion is a
proof step with no counterpart in the TeX.

**Recommendation.**  The manuscript path should terminate at
`manuscriptCoronaMFResidual` / `cdeMFResidual`.  `normMFResidual` and the
`WeakMF` family are legitimate internal infrastructure; they are not legitimate
*load-bearing rungs of a manuscript proof*.

Evidence that this is achievable rather than aspirational: the functoriality
lemma `lem:portable` is already there.  `manuscriptRadicalPortability` has 138
helpers over 28 modules and reaches the foreign rung **zero** times; run with the
patterns widened to catch every residual name, its only hits are
`manuscriptCoronaMFResidual`, `mem_manuscriptCoronaMFResidual_iff`,
`map_manuscriptCoronaMFResidual_le` and
`literal_mark_mem_manuscriptCoronaMFResidual` — the printed object and the printed
functoriality, and nothing else.  That is the shape every badge in this section
should have.

## T2 — `thm:normal-kazhdan`: the printed corona argument is replaced by the universal theorem plus a descent

**Categories (b) and (c).  Manuscript claim: Theorem `thm:normal-kazhdan`,
one of the two central obstruction theorems.  IN FLIGHT — owned by `corona-nk`.**

**Status as of the latest re-run: the replacement exists, the badge does not use
it yet.**  `GroupApproximation/Sofic/CoronaImageNormalKazhdan.lean` is present
and proves the printed corona-image chain, but the closure of
`manuscriptNormalKazhdanObstruction` contains **no** declaration from that module
and no `nk_0*` step; it still routes
`normalKazhdan_le_normMatrixCStarCoronaKernel → normalKazhdan_le_normMFResidual
→ NormMFInvisible.toCoronaMFInvisible`, with 18 foreign-layer helpers.  So this
is now "both routes exist, the manuscript path takes the wrong one" — a
rewiring, not a proof obligation.  The description below is of the route
currently on the manuscript path.

The badge `manuscriptNormalKazhdanObstruction`
(`Sofic/ManuscriptExactWrappers.lean:273`) states the printed proposition with the
printed objects: `Theta : H →* unitary (NormMatrixCStarCorona X)`,
`K ≤ Theta.ker`.  Its proof is one `exact` into
`normalKazhdan_le_normMatrixCStarCoronaKernel`
(`Sofic/NormalKazhdanMFRadical.lean:128`), which does:

```
rho  ──κ⁻¹──▶  NormMatrixCoronaUnitary X
  k ∈ K  ──▶  k ∈ normMFResidual E        (normalKazhdan_le_normMFResidual)
         ──▶  CoronaMFInvisible k          (NormMFInvisible.toCoronaMFInvisible)
         ──▶  k ∈ sigma.ker
```

The printed proof has no such shape.  It fixes one corona representation Θ, passes
to the image `H̄ = Θ(H)`, applies `prop:mf-equivalences` along an exhaustion, and
then runs four named stages — *the moving spectral subspace*, *the tracial deficit
on the corner*, *compression*, *the contradiction* — entirely inside that one
corona.

The four stages **do** exist in Lean, one level further down:
`normalKazhdan_le_normMFResidual` restricts to `rho.range`, gets
`IsOperatorMF rho.range` from `normMFResidual rho.range = ⊥`, upgrades to
`IsWeakMF`, and hands off to
`KazhdanCompressionCore.not_isWeakMF_of_normalKazhdan_le_defect`
(`Sofic/NormalKazhdanCompressionObstruction.lean:47`).  So the mathematics is
present; what is inserted is a strictly stronger ambient statement (all index
types, all ultrafilters) at the top and a descent step
(`toCoronaMFInvisible`) at the bottom, neither of which the manuscript has.

The same shape recurs on `thm:abstract-nk` (`manuscriptAbstractNormalKazhdanObstruction`,
18 abstraction helpers), `cor:intrinsic-nk` (`manuscriptIntrinsicNormalKazhdanRadical`, 20)
and the generated-part corollary (`manuscriptIntrinsicNormalKazhdanPart`, 19).

There is also a second, unused corona-language route already in the file —
`normalKazhdan_le_coronaMFResidual` (`Sofic/NormalKazhdanMFRadical.lean:118`) —
which is itself proved by rewriting with `coronaMFResidual_eq_normMFResidual` and
calling the universal theorem, so it does not fix the issue.

## T2b — the collapse chain bypasses the transport theorem it cites

**Categories (b) and (c).  Independently confirms audit finding R1.  Manuscript
claim: the whole collapse section and the sofic non-MF witness that depends on
it.**

The manuscript's collapse argument cites the Kazhdan transport theorem.  Neither
`manuscriptKazhdanTransport` nor `scaled_transport_both` — both formalized, both
badged — appears anywhere in any collapse badge's closure.  Fifteen collapse
badges, some with 500+ helpers, all `NONE`:

| collapse badge | helpers | transport reached |
| --- | --- | --- |
| `signFree_collapse` | 521 | none |
| `signFreeQuotient_not_isCDEOperatorMF` | 430 | none |
| `literalCommutingLampQuotient_collapse` | 375 | none |
| `literalSignFreeQuotient_isSofic_and_not_isCDEOperatorMF` | 352 | none |
| `commutingLampQuotient_collapse` | 296 | none |
| `literalCommutingLampQuotient_not_isCDEOperatorMF` | 285 | none |
| `commutator_not_zpow_mark` | 255 | none |
| `corona_projection_collapse` | 164 | none |
| `actualCoronaMFResidual_eq_torsionCollapseDefect_of_kazhdan` | 113 | none |
| `actualCoronaMFInvisible_of_torsionWitness` | 96 | none |
| `manuscriptCollapseRadicalReduction` | 81 | none |
| `manuscriptInvolutiveCollapse` | 68 | none |
| `torsionCollapseDefect_le_actualCoronaMFResidual_of_kazhdan` | 53 | none |
| `exists_hs_collapse` | 25 | none |
| `manuscriptInvolutiveCollapsePattern` | 3 | none |

For contrast, the transport theorems *are* reached where the manuscript says
they should be: `manuscriptKazhdanTransport → finiteStageKazhdanTransport`,
`scaled_transport_both → scaled_transport`, `scaled_intertwiner_transport →
scaled_transport`, `manuscriptFixedTensorTransport → scaled_intertwiner_transport,
scaled_transport`.  So the machinery is wired correctly in the transport section
and simply is not used by the section that cites it.

Reproduce with `--format json` and intersect each collapse closure against the
transport declaration names; the check is three lines and worth adding to the
manuscript-path gate.

## T3 — `lem:permanence`(2): residually finite → MF goes through LEF, which the manuscript does not use

**Category (b).  Manuscript claim: Lemma `lem:permanence` clause 2 (tex:2465),
used by `cor:quotclosure` and hence by the Theorem A consequences chain.**

Printed proof (tex:2474–2479):

> For a finite test set F, a finite quotient injective on F, composed with its
> left regular permutation action, is an exact local model; distinct permutations
> differ in some column of a permutation matrix, giving operator-norm separation
> at least 1, and the local-to-corona direction of
> Proposition~\ref{prop:mf-equivalences} concludes.

Lean (`Sofic/OperatorMFPositiveControls.lean:27`):

```
isOperatorMF_of_residuallyFinite
  -> isWeakMF_of_residuallyFinite      (WeakMFTransfer.lean:125)
       -> isLEF_of_residuallyFinite
       -> isWeakMF_of_isLEF            (WeakMFTransfer.lean:121)
  -> IsWeakMF.isOperatorMF             (OperatorMFPositiveControls.lean:20)
       -> normMFResidual_eq_bot_of_isWeakMF
       -> isOperatorMF_of_normMFResidual_eq_bot
```

Two divergences.  First, **LEF**: `RF → LEF → weak-MF` replaces the printed
`RF → exact local model`.  LEF is strictly more general than RF and the word does
not occur in the printed proof of this clause; the permutation-column separation
argument the manuscript describes does survive, inside
`isNormApproximable_of_isLEF` (`WeakMFTransfer.lean`, `normSq_entry_le_sq_l2_opNorm`).
Second, the concluding step is the T1 detour rather than "the local-to-corona
direction of `prop:mf-equivalences`" — though see the note under T4, which makes
this second half milder than it looks.

`isOperatorMF_of_locallyFinite` (clause 3) has the identical profile: 16
abstraction helpers, same route.

## T4 — `prop:mf-equivalences`: the Lean route matches the printed appendix, with one naming inversion

**Category (a), mild.  Manuscript claim: Proposition `prop:mf-equivalences`
(tex:287), Appendix `app:equivalences` (tex:3460).**

Worth stating explicitly because it is the case that looks worst in the raw
numbers (11 abstraction helpers, minimum depth 2) and is in fact largely correct.

`manuscriptMFDefinitionEquivalences` reaches the foreign rung through
`OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one`, whose
`⟸` direction is

```lean
intro h; exact (show IsWeakMF G from ⟨1, by norm_num, h⟩).isOperatorMF
```

i.e. local models → weakly MF → residual trivial → corona embedding.  That is
**exactly** the printed appendix argument, which says: *"local models with
separation constant 1 … make the group weakly MF … Weak MF in turn makes the
norm-MF radical of Definition~\ref{def:radical} trivial, and the block-sum
diagonalization in the proof of Proposition~\ref{prop:univquot}(2) then assembles
the detecting sequences into a single faithful corona representation."*

Two residual observations:

1. **Naming inversion.**  The manuscript locates the diagonalization inside the
   proof of `prop:univquot`(2) and says the weak-to-corona implication is
   *obtained from* it.  In Lean the diagonalization is the standalone
   `isOperatorMF_of_normMFResidual_eq_bot`, and `normMFQuotient_isOperatorMF`
   (= `prop:univquot`(2)) is a two-line corollary of it.  Same mathematics, same
   single location, opposite naming direction.  Not a mismatch; a ledger note.
2. The radical it makes trivial is the foreign rung, not `def:radical` — T1.

## T5 — Conditional packages reached transitively

**Category (d).  Cross-reference `conditional-sweep` for the full catalogue;
what follows is only the *transitive* part.**

`check_non_mf_unconditional.py` currently reports 14 problems over 8 badges.
The closures add the following, none of which that gate sees:

**Genuine, already known at the badge level (no new finding, but the whole API
below them is conditional too).**  `exists_twoGenerated_…_fullMFRadical` and
`exists_group_with_every_nontrivial_quotient_not_isCDEOperatorMF` reach the
entire `DefectRoutingData` API — `cdeMFResidual_eq_top`, `coronaMFResidual_eq_top`,
`isTwoGenerated`, `mapped_defectNormal_eq_top`, `quotientNontrivial`,
`quotient_not_isOperatorMF`, `quotient_not_isCDEOperatorMF`,
`quotient_coronaMFResidual_eq_top` (all `Sofic/TorsionFreeFullMFRadical.lean`) —
each of which requires `DefectRoutingData` or `FournierFacioDefectData`, neither
of which the corpus ever produces.  `operatorMF_recognition_undecidable` reaches
`MarkovMFConsequences.recognition_undecidable`, which requires
`AdianRabinReduction`.  These are the frozen-endpoint and Adian–Rabin surfaces;
they are documented in `notes/NON_MF_CONDITIONAL_INVENTORY.md` and are the *whole
point* of the routing program rather than defects to fix here.

**`IsPointNormMatriciallyStable`, transitively — no longer a finding.**
`MatricialStabilityRadical.fdUnitaryResidual_le_coronaMFResidual`
(`Sofic/MatricialStabilityRadical.lean:120`) carries the stability premise and is
reached from `actualCoronaMFResidual_eq_fdUnitaryResidual` and
`not_isCDEOperatorMF_of_stable_of_fdResidual_ne_bot`.  The premise is genuinely
load-bearing rather than vestigial, and it is also **discharged**:
`Sofic/MatricialStabilityInstances.lean` concludes it for every free group
(`:359`) and for `Multiplicative ℤ` (`:393`), with no literature input, so the
gate no longer reports these two — the sentence here that said it did was
written before that module existed.  See § 6--7 of
`notes/NON_MF_CONDITIONAL_INVENTORY.md` for the claim-strength caveat: clause 3
is discharged only in the contrapositive.

**The bundling-structure class — detected, and off the manuscript path.**
`UltraproductAdjointModel` and `WeightedUltraproductAdjointModel`
(`Sofic/UltraproductKazhdanTransport.lean:413`,
`Sofic/UltraproductScaledTransport.lean`) are corpus-defined and never
discharged, and they are hidden behind a `∀ … → …` in the premise, so the
head-position test — and therefore `check_non_mf_unconditional.py` — is blind to
them.  The `buried` flag was added for exactly this and reports both:

```
ultraproductKazhdanTransport            UltraproductKazhdanTransport.lean:654
    buried:UltraproductAdjointModel
manuscriptKazhdanTransport_ultraproduct ManuscriptKazhdanTransport.lean:93
    conditional:NaturalHSCommutatorVanishing buried:UltraproductAdjointModel
```

Two independent confirmations of the lead's report.  First, the **badged**
`manuscriptKazhdanTransport` (`ManuscriptKazhdanTransport.lean:232`) is *not*
affected: it carries no `UltraproductAdjointModel` and routes through
`finiteStageKazhdanTransport`, which carries none either.  Second, no badge
closure reaches `ultraproductKazhdanTransport`,
`manuscriptKazhdanTransport_ultraproduct`, or `UltraproductAdjointModel` at all —
the conditional lane is genuinely off the manuscript path, not merely deeper
down it.  (`NaturalHSCommutatorVanishing` is flagged on the badged theorem too,
but that is the transport hypothesis the caller supplies, and is a
false positive of the shared discharge fixed point.)

Adding `buried` to the whole corpus produced exactly **three** new badge-level
hits, all one name: `NegativeCornerModel.cornerModel` mentioning `negPredicate`,
a local decidable index predicate. That is benign, and is the honest measure of
this flag's false-positive rate on this corpus — one spurious name for the class
it was built to catch.

**Structure-parameter noise.**  The remaining ~95 conditional hits are helpers
that take a construction datum the caller builds: `IsKazhdanPair` /
`HasNoInvariantVectors`, `NormModel`, `UnitVectorSequence`,
`IsInvolutiveCompressionWitness`, `HSDistVanishing`, `IsSoundIterate`,
`IsAsymptoticIntertwiner`, `IsScaledAsymptoticCommutant`. The discharge fixed
point in `check_non_mf_unconditional.py` marks a structure "never produced" when
no declaration's *conclusion head* is that structure, which misses data built
inline by an anonymous constructor.  Treat these as leads, not findings; they are
`conditional-sweep`'s call, not this document's.  The largest single
concentration — 22 hits, all `UnitVectorSequence`, under
`WeakMFVectorGNS.hermitianAverage_eventually_no_intermediate_eigenvalues`
(`app:finite-stage`) — is **IN FLIGHT** with `fs-gap`.

## T6 — Forward references to later manuscript results

**Category (b)-adjacent, low severity.  Mechanically computed by
`--forward-refs`.**

Seven badges reach a result the manuscript prints later:

| badge (tex line) | reaches | at tex line | depth |
| --- | --- | --- | --- |
| `manuscriptTheoremA` (1344) | `manuscriptBaseHasKazhdanPropertyT` | 1751 | 3 |
| | `literal_mark_ne_one` | 1969 | 2 |
| | `commutator_conjugate_eq_commutator_sq_of_sq_eq_one` | 2011 | 4 |
| `manuscriptTheoremFamily` (1383) | `manuscriptBaseHasKazhdanPropertyT` | 1751 | 3 |
| `literal_uniform_operatorNorm_obstruction` (1357) | `commutator_conjugate_…` | 2011 | 4 |
| `manuscriptFiniteDimensionalConsequences` (1518) | `literal_mark_ne_one` | 1969 | 2 |
| `literal_sixGenerated_finitelyPresented_nonMF` (1680) | `manuscriptBaseHasKazhdanPropertyT` | 1751 | 4 |
| `kazhdanCliffordConstruction` (1250) | `commutator_conjugate_…` | 2011 | 2 |
| `literalSignFreeQuotient_isSofic_and_not_isCDEOperatorMF` (2792) | three `CommutingLampCollapse` results | 2793–2795 | 1–3 |

Every one of these is a forward citation the manuscript makes openly — Theorem A's
proof does depend on the construction of Section 5 and on `prop:witness`.  Listed
so that the *next* forward reference, if it is not announced in the TeX, is
visible as a change rather than as background.

## T7 — Name shadowing: what this tool does and does not catch

Asked specifically about `P13KernelFactorization.toSL3_injective`, a conditional
duplicate said to shadow the unconditional `P13DescentMaster.toSL3_injective`.

**It is already gone.**  `grep -rn toSL3_injective GroupApproximation` returns
only `P13DescentMaster.lean:2610` (the real one), its own docstring, and two call
sites in `LiteralBaseCompleteness.lean:581,888` — both of which name it
**fully qualified** as `P13DescentMaster.toSL3_injective`.  No
`P13KernelFactorization` module or symbol exists in the tree.  Nothing to delete.

**On the general question — can this tool catch that class?  Partly, and the
limits are worth stating precisely.**

* *Indexing*: yes.  The index is keyed by fully qualified name, so two
  same-short-name declarations in different namespaces are distinct nodes and
  neither hides the other.
* *Resolution*: yes, and over-cautiously.  When a reference token resolves in
  scope, the scoped candidates win.  When it does not, the suffix fallback
  emits an edge to **every** declaration in the import closure with that final
  component — so a genuine shadowing pair would appear as *two* edges, both
  marked `~`, from the same call site.  A reviewer sees the ambiguity rather
  than a silent wrong pick.
* *Flagging*: yes, transitively.  A conditional twin reached this way is flagged
  `conditional` or `buried` like any other node, at whatever depth it sits.
* *What is missed*: the tool cannot tell you **which** of an ambiguous pair Lean
  actually elaborates to.  That needs the environment, and this is a source-level
  analyser by mandate.  If a conditional twin and an unconditional twin are both
  in scope, the tool reports the union — correct as a warning, useless as a
  verdict.  Resolving it means reading the call site, as I did above.

So: a shadowing pair inside a badge closure will show up (as a doubled `~` edge
with one side flagged); a shadowing pair whose conditional side is *not* reachable
from any badge will not, because this tool only ever looks at badge closures.
That second gap is real and is why `check_non_mf_unconditional.py`'s corpus-wide
sweep and this closure-walk are complements, not substitutes.

## Positive controls

Badges whose whole closure is clean under all four questions, worth recording so
that the findings above are read as specific rather than as a blanket complaint:

* `hasKazhdanPropertyT_of_finite` — 2 helpers, both definitions, no repository
  lemma.  The proof is `⟨Finset.univ, 1, one_pos, …⟩` summing the orbit of an
  almost-invariant unit vector: verbatim the printed "the whole group with
  tolerance 1 is a Kazhdan pair, by orbit averaging" (tex:1094).
* `manuscriptTheoremB` — 22 helpers, 5 modules, zero flags.
* `manuscriptMFRadical` — 7 helpers, uses `manuscriptCoronaMFResidual` only.
* `manuscriptRadicalPortability` (`lem:portable`) — 138 helpers, and every
  residual it touches is the printed one.  See the recommendation under T1.
* `manuscriptFiniteDimensionalConsequences`, `manuscriptLiteralPresentation`,
  `literal_mark_ne_one`, `p13CompletenessEquiv`, `manuscriptCyclicCalibration`,
  `cyclicBase_exactModel_package`, `literal_no_faithful_corona_subalgebra_target`,
  `commutator_not_zpow_mark`, `manuscriptUniverseRelativeMaximalGroupCStar`, the
  three `ProperProjectionCompression` badges, `exists_hsClose_adjointFar`,
  `exists_hs_collapse`, `manuscriptFaithfulTraceAndStableFiniteness`,
  `manuscriptUnitaryLifting`, `manuscriptUnitaryCoronaEquivalence`,
  `manuscriptMarkedKazhdanPattern`, `compressionGroup_transport_both` — zero flags
  at depth ≤ 6.

## Known-in-flight paths

Do not read the following as unattended defects:

| path | owner |
| --- | --- |
| ultraproduct Kazhdan transport — `manuscriptKazhdanTransport`, `scaled_transport_both`, `manuscriptIntertwinerTransport`, `scaled_intertwiner_transport`, `manuscriptFixedTensorTransport` (the `IsScaledAsymptoticCommutant` / `IsScaledAsymptoticIntertwinerOf` conditionals, 5–6 per closure) | `up-ambient`, `up-endgame`, `up-fix-proj` |
| corona-image normal-Kazhdan route — T2 in full.  `Sofic/CoronaImageNormalKazhdan.lean` now exists and proves the printed chain; the badge is not rewired to it yet, so the closure is unchanged | `corona-nk` |
| central-sign criterion — `Sofic/ManuscriptCentralSignCriterion.lean` now inhabits the same `Prop` by the transport route; the badged `manuscriptCentralSignCriterion` still routes `defectSquare_centralInvolution_mem_normMatrixCStarCoronaKernel → … → finiteNormal_le_normMFResidual` (T1), and the reroute of `LiteralNonMFEndpoint.literal_centralSignCriterion` is authorized and in progress | central-sign lane |
| finite-stage spectral gap — `hermitianAverage_eventually_no_intermediate_eigenvalues` and its 22 `UnitVectorSequence` hits | `fs-gap` |
| dyadic model objects | `dyadic` |
| torsion-free rank invariant | `tfrank` |

---

# Appendix: per-badge closure profile

`H` = distinct helper declarations reachable at depth ≤ 6; `M` = modules they
live in; `D` = greatest depth reached; `C/B/L/A` = conditional / buried-package /
literature-roster / foreign-abstraction helpers.  Order is manuscript order.
Produced by `scripts/trace_manuscript_deps.py --summary`.

```
    H    M  D   C/ B/ L/ A   badge
  145   20  6   0/ 0/ 0/11   ManuscriptExactWrappers.manuscriptMFDefinitionEquivalences
   46    8  6   0/ 0/ 0/ 0   ManuscriptExactWrappers.manuscriptUnitaryLifting
   48    8  6   0/ 0/ 0/ 0   ManuscriptExactWrappers.manuscriptUnitaryCoronaEquivalence
  132   27  6   1/ 0/ 0/ 2   KazhdanAsymptoticCommutant.manuscriptKazhdanTransport
   94   19  6   0/ 0/ 0/ 7   KazhdanCompressionCore.manuscriptCentralSignCriterion
  218   27  6   1/ 0/ 0/ 3   KazhdanCliffordConstruction.kazhdanCliffordConstruction
  375   58  6   1/ 0/ 0/11   LiteralNonMFEndpoint.manuscriptTheoremA
  271   44  6   0/ 1/ 0/ 3   LiteralNonMFEndpoint.negativeCorner_kazhdanTransport_contradiction
  128   25  6   1/ 0/ 0/ 6   LiteralUniformObstruction.literal_uniform_operatorNorm_obstruction
  521   75  6   0/ 0/ 0/ 3   LiteralSignFreeQuotient.signFree_collapse
  430   61  6   0/ 0/ 0/ 1   LiteralSignFreeQuotient.signFreeQuotient_not_isCDEOperatorMF
  255   23  6   0/ 0/ 0/ 0   LiteralSignFreeQuotient.commutator_not_zpow_mark
   99   28  6   0/ 0/ 0/ 4   LiteralNonMFEndpoint.manuscriptTheoremD
  290   42  6   0/ 0/ 0/ 8   NonMFImpact.witness_sofic_hyperlinear_nonMF
  103    4  6   0/ 0/ 0/ 0   LiteralNonMFPresentation.manuscriptLiteralPresentation
  226   40  6   1/ 0/ 0/ 0   LiteralSixGenerator.literal_sixGenerated_finitelyPresented_nonMF
   90   11  6   1/ 0/ 0/ 0   LiteralTietzePresentation.manuscriptTietzeSixGeneratorPresentation
  221   48  6   2/ 0/ 0/ 0   LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT
  468   25  6   0/ 0/ 0/ 0   P13DescentMaster.p13CompletenessEquiv
  709   65  6   1/ 0/ 0/ 0   LiteralBaseCompleteness.baseAffineEquiv
   35    1  6   0/ 0/ 0/ 0   ManuscriptExactWrappers.manuscriptCliffordConstruction
  162    8  4   1/ 0/ 0/ 0   ManuscriptExactWrappers.manuscriptLinearModel
  179   15  6   0/ 0/ 0/ 0   LiteralNonMFLinearWitness.literal_mark_ne_one
    0    0  0   0/ 0/ 0/ 0   commutator_conjugate_eq_commutator_sq_of_sq_eq_one
  116   10  6  22/ 0/ 0/48   WeakMFVectorGNS.hermitianAverage_eventually_no_intermediate_eigenvalues
  144   25  6   6/ 0/ 0/ 2   ScaledKazhdanTransport.scaled_transport_both
  148   28  6   1/ 0/ 0/ 2   IntertwinerKazhdanTransport.manuscriptIntertwinerTransport
  160   27  6   5/ 0/ 0/ 2   IntertwinerKazhdanTransport.scaled_intertwiner_transport
  103   26  6   6/ 0/ 0/ 1   TensorPowerTransport.manuscriptFixedTensorTransport
   50    9  6   0/ 0/ 0/ 0   ManuscriptExactWrappers.manuscriptMarkedKazhdanPattern
   16    8  5   0/ 0/ 0/ 0   ManuscriptExactWrappers.ManuscriptHSInvisible
  114   27  6   1/ 0/ 0/11   ManuscriptExactWrappers.manuscriptFiniteNormalObstructionCriterion
   33   11  6   0/ 0/ 0/ 0   KazhdanAsymptoticCommutant.compressionGroup_transport_both
  189   36  6   1/ 0/ 0/16   KazhdanAsymptoticCommutant.manuscriptCompressionRadical
  205   37  6   0/ 0/ 0/18   ManuscriptExactWrappers.manuscriptNormalKazhdanObstruction
    2    1  2   0/ 0/ 0/ 0   hasKazhdanPropertyT_of_finite
  197   38  6   0/ 0/ 0/18   ManuscriptExactWrappers.manuscriptAbstractNormalKazhdanObstruction
  181   40  6   0/ 0/ 0/20   ManuscriptExactWrappers.manuscriptIntrinsicNormalKazhdanRadical
  147   35  6   0/ 0/ 0/19   ManuscriptExactWrappers.manuscriptIntrinsicNormalKazhdanPart
   22    5  6   0/ 0/ 0/ 0   ManuscriptExactWrappers.manuscriptTheoremB
  190   15  6   0/ 0/ 0/ 0   LiteralFiniteDimensionalObstruction.manuscriptFiniteDimensionalConsequences
    1    1  1   0/ 0/ 0/ 0   ManuscriptExactWrappers.manuscriptInvariantSizePrinciple
   11    3  3   0/ 0/ 0/ 0   manuscriptChainConditionRigidity
   13    3  4   0/ 0/ 0/ 0   TensorInvariantRigidity.manuscriptTensorInvariantRigidity
    8    3  5   0/ 0/ 0/ 0   ClosedEnvelopeCompression.manuscriptEnvelopeCompressionBlind
  121    5  6   0/ 0/ 0/ 0   LiteralCyclicCalibration.manuscriptCyclicCalibration
  129    8  6   0/ 0/ 0/ 0   CyclicBaseLEFObstruction.cyclicBase_exactModel_package
  350   56  6   0/ 0/ 0/11   ScalingFamilyEndpoint.manuscriptTheoremFamily
    7    4  3   0/ 0/ 0/ 0   ManuscriptExactWrappers.manuscriptMFRadical
  149   32  6   0/ 0/ 0/ 0   ManuscriptExactWrappers.manuscriptRadicalPortability
  105   15  6   0/ 0/ 0/13   ManuscriptExactWrappers.manuscriptUniversalMFQuotient
   61   13  6   0/ 0/ 0/ 9   ManuscriptExactWrappers.manuscriptExactRadicalFromCandidateQuotient
   23   12  5   0/ 0/ 0/ 2   ManuscriptExactWrappers.manuscriptRadicalReductionToQuotient
   15    8  3   0/ 0/ 0/ 2   mem_actualCoronaMFClosure_iff
   92   19  6   0/ 0/ 0/12   manuscriptRelationClosure
   59   15  6   3/ 0/ 0/ 2   manuscriptSoundIterationClosure
  309   52  6   1/ 0/ 0/ 2   LiteralNonMFConsequences.literal_no_faithful_corona_subalgebra_target
   15    9  3   0/ 0/ 0/ 2   IsOperatorMF.subgroup
   66   13  6   0/ 0/ 0/16   isOperatorMF_of_residuallyFinite
   61   13  6   0/ 0/ 0/16   isOperatorMF_of_locallyFinite
  339   58  6   1/ 0/ 0/15   LiteralMFQuotientControls.manuscriptQuotientNonclosure
    9    6  2   0/ 0/ 0/ 0   MatricialStabilityRadical.actualCoronaMFResidual_le_fdUnitaryResidual
   59   12  6   1/ 0/ 0/ 2   MatricialStabilityRadical.actualCoronaMFResidual_eq_fdUnitaryResidual
   51   14  6   2/ 0/ 0/ 2   MatricialStabilityRadical.not_isCDEOperatorMF_of_stable_of_fdResidual_ne_bot
    3    1  2   0/ 0/ 0/ 0   ManuscriptExactWrappers.manuscriptInvolutiveCollapsePattern
   68   23  6   0/ 0/ 0/ 1   ManuscriptExactWrappers.manuscriptInvolutiveCollapse
  164   41  6   0/ 0/ 0/ 3   ProjectionCompressionCollapse.corona_projection_collapse
   96   27  6   0/ 0/ 0/ 1   TorsionSpectralCollapse.actualCoronaMFInvisible_of_torsionWitness
   53   12  6   0/ 0/ 0/ 0   TorsionSpectralCollapse.torsionCollapseDefect_le_actualCoronaMFResidual_of_kazhdan
  113   20  6   0/ 0/ 0/12   TorsionSpectralCollapse.actualCoronaMFResidual_eq_torsionCollapseDefect_of_kazhdan
  352   49  6   1/ 0/ 0/ 0   CommutingLampQuotientSofic.literalSignFreeQuotient_isSofic_and_not_isCDEOperatorMF
  296   56  6   0/ 0/ 0/ 3   CommutingLampCollapse.commutingLampQuotient_collapse
  375   55  6   1/ 0/ 0/ 1   CommutingLampCollapse.literalCommutingLampQuotient_collapse
  285   38  6   1/ 0/ 0/ 0   CommutingLampCollapse.literalCommutingLampQuotient_not_isCDEOperatorMF
   81   24  6   0/ 0/ 0/11   ManuscriptExactWrappers.manuscriptCollapseRadicalReduction
   27   11  6   0/ 0/ 0/ 0   ManuscriptExactWrappers.manuscriptDefectSaturation
   20    5  6   0/ 0/ 0/ 0   ManuscriptExactWrappers.manuscriptFaithfulTraceAndStableFiniteness
  319   38  6   1/ 0/ 0/18   LiteralWitnessConsequences.literalWitness_locallyFiniteKernel_nonMF
  338   45  6   0/ 0/ 0/16   LiteralLEFExtension.literalWitness_LEFKernel_integerExtension_nonMF
   91   16  6   1/ 0/ 0/10   MarkedGroupSpace.isClosed_operatorMFLocus
   69   13  6   1/ 0/ 0/ 9   MarkedGroupSpace.isOpen_compl_operatorMFLocus
   95   17  6   1/ 0/ 0/10   MarkedGroupSpace.exists_wordBall_cylinder_subset_compl_operatorMFLocus
  199   29  6   1/ 0/ 0/ 6   LiteralUniversalHorn.manuscriptLiteralUniversalHorn
  217   31  6   1/ 0/ 0/ 6   LiteralMarkedCylinder.literal_nonempty_clopen_nonMF_cylinder
   16    9  3   0/ 0/ 0/ 2   MarkovMFConsequences.operatorMF_subgroup_hereditary
  109   26  6   0/ 1/ 0/ 2   MarkovMFConsequences.exists_finitelyPresented_nonOperatorMF
   10    3  4   1/ 0/ 0/ 0   MarkovMFConsequences.operatorMF_recognition_undecidable
  145   33  6   1/ 1/ 0/ 3   ProductMultiplicity.manuscriptInfiniteMultiplicity
  113   32  6   1/ 0/ 0/ 3   ContinuumMultiplicity.manuscriptContinuumMultiplicity
   23    7  4   0/ 0/ 0/ 0   HilbertSchmidtAdjointGap.exists_hsClose_adjointFar
   25    4  3   0/ 0/ 0/ 0   NormModel.exists_hs_collapse
  295   49  6   1/ 0/ 0/ 0   FaithfullyTracedCoordinates.manuscriptFaithfullyTracedCoordinateNoGo
    0    0  0   0/ 0/ 0/ 0   finiteSubgroup_eq_bot_of_isMulTorsionFree
  129   27  6   6/ 0/ 0/14   FullMFRadicalEndpoint.exists_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical
   75   16  6   8/ 0/ 0/ 3   FullMFRadicalEndpoint.exists_group_with_every_nontrivial_quotient_not_isCDEOperatorMF
   27    3  6   0/ 0/ 0/ 0   manuscriptUniverseRelativeMaximalGroupCStar
   16    1  4   0/ 0/ 0/ 0   ProperProjectionCompression.isometry_not_isUnit
   17    1  5   0/ 0/ 0/ 0   ProperProjectionCompression.not_isStablyFiniteRing
   20    2  4   0/ 0/ 0/ 0   ProperProjectionCompression.no_faithfulTracialState
    2    1  2   0/ 0/ 0/ 0   QuasiRegularWitness.baseVector_apply_base
```

All 100 badges are listed.  `grep -c 'leanverified{' non_mf_groups_exist.tex`
returns 100 at this snapshot; the bare `grep -c leanverified` returns 102, the
extra two being the `\newcommand` definitions in the preamble.
