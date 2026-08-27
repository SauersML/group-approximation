import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarConsequence
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefinitions
import GroupApproximation.Analysis.ReducedGroupCStarMFAlgebra
import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Algebra.GroupTorsionFree

/-!
# Sentence-level claims of the abstract and Introduction

`non_mf_groups_exist.tex`, the `abstract` environment and `\section{Introduction}`,
every sentence that asserts mathematics (as opposed to pure exposition,
attribution, or naming), keyed by the fleet's per-sentence audit identifiers.

Most of these sentences are the abstract's or the Introduction's own summary
of a theorem, definition, or remark that is *already* proved and wired
elsewhere in the tree (`thm:headline`, `thm:compression-criterion`, the
Introduction's MF definitions, the reduced group `C*`-algebra facts).  Nothing
new is proved for those; each gets a thin declaration under the sentence's
own key so that the abstract's and Introduction's own lines can eventually
carry a `\leanverified` tag distinct from the one at the theorem's own
location — at present neither the abstract nor most of the Introduction's
definitional paragraphs carry any tag at all, unlike the theorem statements
they summarize.

One sentence — the abstract's closing claim about a finitely presented
torsion-free full-radical group — belongs to a different lane
(`ff-theoremC`, `thm:torsion-free`) and is recorded as a `WIRING` stub.

Sentences that are pure attribution, naming, or scope statements rather than
mathematical assertions are listed in the module docstring below rather than
given a `Prop`; see the fleet report for the full accounting.

## Rows deliberately not given a declaration

* `8df1276930c1` ("not every countable group is MF") is already wired at
  `non_mf_groups_exist.tex:84` to `CountableNonMF.manuscriptNotEveryCountableGroupIsMF`.
* `90419fdeb449` ("Let `L ≤ G` and `K ◁ G` have property (T)") is pure
  hypothesis setup, folded into the combined declaration for `5d97364ce1c1`.
* `bb819e9d6be7` ("The MF radical" section) is already wired at
  `non_mf_groups_exist.tex:449` to `PrintedDefinitions.manuscriptCoronaImagesAndTargets`.
* `5b19b83a9834` (Khanh–Thanh identify `H` with the unit group of the binary
  Leavitt algebra) is pure attribution: grepping the tree for `KhanhThanh` and
  for "unit group" finds no such declaration, and none is needed, since this
  development defines `H = EL₁₂(R)` directly rather than deriving it from that
  identification.  It is not a proof dependency of anything below.
* `7ab17fc64b15` ("We use this operator norm convention throughout") and
  `63aa15cf8902` (the strong-convergence convention used elsewhere in the
  literature) are scope statements about which convention is in force, not
  independently checkable mathematical claims; nothing in the tree formalizes
  the strong-convergence alternative, and none is needed here.
* `d31180a98ce2` ("We call a homomorphism `G → U(𝒬_𝐝)` a corona
  homomorphism") is pure terminology, given a `Type`-valued abbreviation below
  with no proof obligation.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open ReducedGroupCStarTrace
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Abstract: `90419fdeb449` + `5d97364ce1c1`

"Let `L ≤ G` and `K ◁ G` have property (T).  If `K` is contained in the
one-sided compression defect of `L`, then `K` lies in the MF radical of
`G`." -/

/-- **Abstract summary of Theorem A (`thm:compression-criterion`).**  Reuses
the first clause of `PrintedCriterion.manuscriptOneSidedCompressionCriterion`,
already proved and wired at the theorem's own location; nothing new is
proved here. -/
def AbstractCompressionRadicalMembership : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
      ∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
        K ≤ printedDefect L → K ≤ manuscriptCoronaMFResidual G

theorem manuscriptAbstractCompressionRadicalMembership :
    AbstractCompressionRadicalMembership :=
  fun G _ _ L hL K _ hK hKD ↦
    (manuscriptOneSidedCompressionCriterion G L hL).1 K hK hKD

/-! ## Abstract: `22127e78d485`

"For `H = EL₁₂(L_{𝔽₂}(1,2))`, this defect equals `H`." -/

/-- **Abstract: the printed defect at the compressor `L = corner` equals
`H`.**  `L` is the printed upper-left `EL₃(R)` corner,
`RankTwelveEndpoint.corner`; the equality `𝔇_H(L) = H` is
`printedDefect corner = ⊤`, already proved unconditionally. -/
def AbstractDefectEqualsH : Prop :=
  printedDefect RankTwelveEndpoint.corner = ⊤

theorem manuscriptAbstractDefectEqualsH : AbstractDefectEqualsH :=
  RankTwelveEndpoint.printedDefect_eq_top_of_configuration
    RankTwelveEndpoint.printedDefectConfiguration

/-! ## Abstract: `ddc60fc24807`

"The group `H` is finitely generated, simple, has property (T), and has
trivial image under every homomorphism to an MF group." -/

/-- **Abstract summary of the structural clauses of `thm:headline`.**  Reuses
`RankTwelveEndpoint.finitelyGenerated` and
`manuscriptBinaryLeavittHeadline`; nothing new is proved here. -/
def AbstractHeadlineProfile : Prop :=
  Group.FG RankTwelveEndpoint.H ∧ RankTwelveEndpoint.HeadlineConclusion

theorem manuscriptAbstractHeadlineProfile : AbstractHeadlineProfile :=
  ⟨RankTwelveEndpoint.finitelyGenerated, manuscriptBinaryLeavittHeadline⟩

/-! ## Abstract: `8926d888e9b1`

"Consequently, `C*_r(H)` is a separable stably finite `C*`-algebra that is
not MF." -/

/-- **Abstract summary of the reduced-`C*` clause of `thm:headline`.**  This
is exactly `ReducedCStarConsequence`; the declaration exists so the abstract's
own line can carry a `\leanverified` tag distinct from the one at
`thm:headline` itself. -/
theorem manuscriptAbstractReducedCStarConsequence : ReducedCStarConsequence :=
  manuscriptReducedCStarConsequence

/-! ## Abstract: `aedc3c5c6430`

"We also construct a finitely presented torsion-free property-(T) group with
full MF radical; every nontrivial quotient of it again has full MF radical." -/

/-- **Abstract summary of `thm:torsion-free` (Theorem C).**  The construction
belongs to the `ff-theoremC` lane. -/
def AbstractTorsionFreeFullRadicalConstruction : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
    Group.FG Q ∧ IsPowerTorsionFree Q ∧ HasKazhdanPropertyT.{0, 0} Q ∧
      manuscriptCoronaMFResidual Q = ⊤ ∧
      ∀ (L : Type) (_ : Group L) (_ : Countable L) (r : Q →* L),
        Function.Surjective r → Nontrivial L → manuscriptCoronaMFResidual L = ⊤

-- WIRING(ff-theoremC): replaced by coordinator
theorem manuscriptAbstractTorsionFreeFullRadicalConstruction :
    AbstractTorsionFreeFullRadicalConstruction := by
  sorry

/-! ## Introduction: `88e8012cb87e`

"A countable group `G` is MF~[CDE] if there are positive integers `d_n` and
maps `V_n : G → U(d_n)`, with `V_n(1)=1`, such that
`‖V_n(gh)-V_n(g)V_n(h)‖ → 0` (`g,h ∈ G`), and
`limsup_n ‖V_n(g)-1‖ > 0` (`g ∈ G ∖ {1}`)." -/

/-- **The Introduction's operator-norm MF definition, unbundled.**  Reuses
`PrintedDefinitions.PrintedMFUnitaryModels`, already proved equivalent to
`IsCDEOperatorMF`.

Two deviations are carried over from that module's own docstring, not
introduced here: the multiplicative-defect clause is "eventually `≤ ε` for
every `ε`" rather than a literal `Tendsto`, and the separation clause is
"eventually `≥` a fixed `delta`" for *all* pairs `g ≠ h`, which is stronger
than the printed `limsup > 0` restricted to `h = 1`.  A third gap is not
resolved by this wrapper: `V_n(1) = 1` is not tracked separately by the
underlying `WeakMFApproximation` data, and no normalization argument
recovering it is proved here; see the fleet report for this lane. -/
theorem manuscriptIntroductionMFDefinition : PrintedMFUnitaryModels :=
  manuscriptMFUnitaryModels

/-! ## Introduction: `72258081fa1d`

"Here `⊕_n M_{d_n}(ℂ)` is the ideal of sequences `(x_n)` for which
`‖x_n‖ → 0`." -/

/-- **The Introduction's description of the corona's denominator.** -/
def IntroductionNullIdealIsFadingSequences : Prop :=
  ∀ (X : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
      [∀ n, Nonempty (X n)] (a : BoundedMatrixSequence X),
    a ∈ nullMatrixSequenceIdeal X Filter.cofinite ↔
      Filter.Tendsto (fun n ↦ ‖a n‖) Filter.atTop (nhds 0)

theorem manuscriptIntroductionNullIdealIsFadingSequences :
    IntroductionNullIdealIsFadingSequences :=
  fun X _ _ _ a ↦ mem_nullMatrixSequenceIdeal_cofinite_iff X a

/-! ## Introduction: `02dd46f90a1b`

"A separable `C*`-algebra is MF if it embeds in a norm matrix corona." -/

/-- **The Introduction's `C*`-algebra MF definition, literally.**  This is
the unfolding of `Analysis.MFAlgebra.IsMFAlgebra`. -/
def IntroductionSeparableCStarAlgebraIsMFDef : Prop :=
  ∀ (A : Type) [NonUnitalCStarAlgebra A],
    IsMFAlgebra A ↔ (TopologicalSpace.SeparableSpace A ∧ HasMFEmbedding A)

theorem manuscriptIntroductionSeparableCStarAlgebraIsMFDef :
    IntroductionSeparableCStarAlgebraIsMFDef :=
  fun _ _ ↦ Iff.rfl

/-! ## Introduction: `b329cfe7a94c`

"For a countable group `G`, the algebra `C*_r(G)` is separable and its
faithful canonical trace makes it stably finite." -/

/-- **The Introduction's general reduced-`C*`-algebra step.**  Reuses
`reducedGroupCStar_separable_stablyFinite`; nothing new is proved here. -/
def IntroductionReducedCStarSeparableStablyFinite : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    TopologicalSpace.SeparableSpace (ReducedGroupCStar G) ∧
      IsStablyFiniteCStarAlgebra (ReducedGroupCStar G)

theorem manuscriptIntroductionReducedCStarSeparableStablyFinite :
    IntroductionReducedCStarSeparableStablyFinite :=
  fun G _ _ ↦ reducedGroupCStar_separable_stablyFinite G

/-! ## Introduction: `83ce7b35edb0`

"The group `H` above gives a non-MF algebra of this form." -/

/-- **The Introduction's restatement that `C*_r(H)` is non-MF.** -/
def IntroductionHGivesNonMFAlgebraOfThisForm : Prop :=
  ¬ IsMFAlgebra (ReducedGroupCStar RankTwelveEndpoint.H)

theorem manuscriptIntroductionHGivesNonMFAlgebraOfThisForm :
    IntroductionHGivesNonMFAlgebraOfThisForm :=
  manuscriptReducedCStarConsequence.2.2

/-! ## Introduction: `d31180a98ce2`

"We call a homomorphism `G → U(𝒬_𝐝)` a corona homomorphism." -/

/-- **Pure terminology.**  The development already uses homomorphisms of
exactly this shape throughout (`ActualCoronaMFInvisible`, `LiteralMFKernels`)
without a separate name; this abbreviation records the printed name for that
shape.  No proof obligation: it is `Type`-valued, not `Prop`-valued. -/
abbrev CoronaHomomorphism (G : Type) [Group G] (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] : Type :=
  G →* unitary (NormMatrixCStarCorona (fun n ↦ X n))

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
