import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarConsequence
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefinitions
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedModelSeparationConverse
import GroupApproximation.Manuscript.NonMF.TorsionFreeTheoremC
import GroupApproximation.Analysis.ReducedGroupCStarMFAlgebra
import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.WeakMFUltraproduct
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
torsion-free full-radical group — is a weakening of `thm:torsion-free`
(Theorem C), whose construction belongs to a different lane (`ff-theoremC`);
it is proved here by destructuring Theorem C's own conclusion, carrying
Theorem C's two cited-input structures as leading hypotheses.

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

/-- **Abstract summary of `thm:torsion-free` (Theorem C).**  A weakening of
`Manuscript.NonMF.TheoremC.PrintedTorsionFreeFullMFRadical`: the
two-generation, finite-presentation, and acylindrical-hyperbolicity conjuncts
are dropped, keeping ordinary finite generation, ordinary torsion-freeness,
property `(T)`, and the radical clause, stated with the same
`manuscriptCoronaMFResidual` constant Theorem C itself uses. -/
def AbstractTorsionFreeFullRadicalConstruction : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
    Group.FG Q ∧ IsPowerTorsionFree Q ∧ HasKazhdanPropertyT.{0, 0} Q ∧
      manuscriptCoronaMFResidual Q = ⊤ ∧
      ∀ (L : Type) (_ : Group L) (_ : Countable L) (r : Q →* L),
        Function.Surjective r → Nontrivial L → manuscriptCoronaMFResidual L = ⊤

/-- **The abstract's summary follows from Theorem C.**
`NonMF.TheoremC.manuscriptTorsionFreeFullMFRadical` (from
`Manuscript/NonMF/TorsionFreeTheoremC.lean`, now landed) supplies `Q` together
with `IsTwoGenerated Q`, `Group.IsFinitelyPresented Q`, `IsPowerTorsionFree Q`,
`TorsionFree.IsAcylindricallyHyperbolic Q`, `HasKazhdanPropertyT Q`,
`manuscriptCoronaMFResidual Q = ⊤`, and the two quotient clauses (the printed
theorem's exact statement, `PrintedTorsionFreeFullMFRadical`).

Countability of `Q` is not one of Theorem C's printed conjuncts, so it is
derived here rather than assumed: a finitely presented group is the
surjective image of a finite-rank free group, and a free group on a finite
(hence countable) generating set is countable
(`instance : [Countable α] → Countable (FreeGroup α)`), so the surjection's
target is countable too.  Ordinary finite generation is read off the printed
two-generation witness directly, avoiding a second detour through finite
presentation. -/
theorem manuscriptAbstractTorsionFreeFullRadicalConstruction
    (I : NonMF.TheoremC.LiteratureInputs)
    (hHull : NonMF.TorsionFree.HullInputs.{0}) :
    AbstractTorsionFreeFullRadicalConstruction := by
  obtain ⟨Q, instQ, ⟨x, y, hxy⟩, hFP, hTF, -, hKazhdan, hRad, hquot, -⟩ :=
    NonMF.TheoremC.manuscriptTorsionFreeFullMFRadical I hHull
  have hFG : Group.FG Q :=
    Group.fg_def.mpr ((Subgroup.fg_iff ⊤).mpr
      ⟨{x, y}, hxy, (Set.finite_singleton y).insert x⟩)
  have hCountQ : Countable Q := by
    obtain ⟨n, φ, hφ, -⟩ := hFP.out
    exact hφ.countable
  exact ⟨Q, instQ, hCountQ, hFG, hTF, hKazhdan, hRad,
    fun L instL _ r hr hL ↦ hquot L instL r hr hL⟩

/-! ## Introduction: `88e8012cb87e`

"A countable group `G` is MF~[CDE] if there are positive integers `d_n` and
maps `V_n : G → U(d_n)`, with `V_n(1)=1`, such that
`‖V_n(gh)-V_n(g)V_n(h)‖ → 0` (`g,h ∈ G`), and
`limsup_n ‖V_n(g)-1‖ > 0` (`g ∈ G ∖ {1}`)."

The printed clause `V_n(1) = 1` is not tracked by the repository's
`WeakMFApproximation` data (its coordinate maps need only be unitary-valued),
and earlier wrappers of this sentence left that clause unproved.  This section
proves it instead of dropping it: left-multiplying every coordinate of a
`WeakMFApproximation` by the conjugate transpose of its own value at `1`
fixes the identity coordinate to `1` exactly, changes no separation (left
multiplication by a unitary is an isometry of the operator norm), and at
worst doubles each multiplicative defect -- the same normalization already
used, at a single finite set, by
`MFRecognition.LocalityAndCertificates.exists_localModel_of_isOperatorMF`;
what is new here is running it along the whole sequence at once, which is
what the printed *sequential* definition needs.

Combined with `PrintedModelSeparationConverse.isCDEOperatorMF_of_limsup_separating_unitary_models`
(already unconditional, and needing no `V_n(1)=1` hypothesis for the converse
direction), this gives a genuine two-sided equivalence with `IsCDEOperatorMF`
in the fully literal printed form, including the `V_n(1)=1` clause. -/

/-- **The algebraic core of the normalization, isolated from the group.**  For
unitary matrices `u, p, q, w`, left-multiplying `p` and `q` by `uᴴ` changes
their product's discrepancy from `w` by at most the discrepancy of `u` from
being idempotent.  Proved by the same splitting-and-peeling technique as
`MFRecognition.LocalityAndCertificates.exists_localModel_of_isOperatorMF`
(there specialized to `w = p = q = u`, the identity coordinate itself). -/
theorem norm_conjTranspose_mul_sub_conjTranspose_mul_mul_le
    {Y : Type} [Fintype Y] [DecidableEq Y] {u p q w : Matrix Y Y ℂ}
    (hu : u ∈ Matrix.unitaryGroup Y ℂ) (hp : p ∈ Matrix.unitaryGroup Y ℂ)
    (hq : q ∈ Matrix.unitaryGroup Y ℂ) :
    ‖Matrix.conjTranspose u * w -
        (Matrix.conjTranspose u * p) * (Matrix.conjTranspose u * q)‖ ≤
      ‖w - p * q‖ + ‖u - u * u‖ := by
  have hustar : Matrix.conjTranspose u ∈ Matrix.unitaryGroup Y ℂ := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hu
  have hone : ‖(1 : Matrix Y Y ℂ) - Matrix.conjTranspose u‖ = ‖u - u * u‖ := by
    rw [show (1 : Matrix Y Y ℂ) - Matrix.conjTranspose u =
        Matrix.conjTranspose ((1 : Matrix Y Y ℂ) - u) by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one],
      Matrix.l2_opNorm_conjTranspose,
      show u - u * u = u * ((1 : Matrix Y Y ℂ) - u) by rw [mul_sub, mul_one],
      CStarRing.norm_mem_unitary_mul _ hu]
  have hsplit : Matrix.conjTranspose u * w -
      (Matrix.conjTranspose u * p) * (Matrix.conjTranspose u * q) =
        Matrix.conjTranspose u * (w - p * (Matrix.conjTranspose u * q)) := by
    rw [mul_sub]; simp only [mul_assoc]
  have hmid : ‖p * q - p * (Matrix.conjTranspose u * q)‖ =
      ‖(1 : Matrix Y Y ℂ) - Matrix.conjTranspose u‖ := by
    rw [show p * q - p * (Matrix.conjTranspose u * q) =
        p * (((1 : Matrix Y Y ℂ) - Matrix.conjTranspose u) * q) by
      rw [sub_mul, one_mul, mul_sub],
      CStarRing.norm_mem_unitary_mul _ hp,
      CStarRing.norm_mul_mem_unitary _ hq]
  calc ‖Matrix.conjTranspose u * w -
          (Matrix.conjTranspose u * p) * (Matrix.conjTranspose u * q)‖
      = ‖w - p * (Matrix.conjTranspose u * q)‖ := by
        rw [hsplit, CStarRing.norm_mem_unitary_mul _ hustar]
    _ ≤ ‖w - p * q‖ + ‖p * q - p * (Matrix.conjTranspose u * q)‖ := by
        rw [← sub_add_sub_cancel w (p * q) (p * (Matrix.conjTranspose u * q))]
        exact norm_add_le _ _
    _ = ‖w - p * q‖ + ‖(1 : Matrix Y Y ℂ) - Matrix.conjTranspose u‖ := by rw [hmid]
    _ = ‖w - p * q‖ + ‖u - u * u‖ := by rw [hone]

/-- **The algebraic core of the separation preservation.**  Left
multiplication by a unitary conjugate transpose is an isometry, so it carries
the identity-comparison exactly to the original separation. -/
theorem norm_conjTranspose_mul_sub_one {Y : Type} [Fintype Y] [DecidableEq Y]
    {u p : Matrix Y Y ℂ} (hu : u ∈ Matrix.unitaryGroup Y ℂ) :
    ‖Matrix.conjTranspose u * p - 1‖ = ‖p - u‖ := by
  have hstar : Matrix.conjTranspose u * u = 1 := by
    have h := hu
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  have hustar : Matrix.conjTranspose u ∈ Matrix.unitaryGroup Y ℂ := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hu
  rw [show Matrix.conjTranspose u * p - 1 = Matrix.conjTranspose u * (p - u) by
    rw [mul_sub, hstar],
    CStarRing.norm_mem_unitary_mul _ hustar]

section NormalizedMap

variable {G : Type} [Group G]

/-- The normalized coordinate map: `u_n⁻¹ · V_n`, with `u_n = V_n(1)` and the
inverse read as the conjugate transpose (`u_n⁻¹ = u_nᴴ` for a unitary
`u_n`). -/
def normalizedMap (A : WeakMFApproximation G) (n : ℕ) (g : G) :
    Matrix (A.model n) (A.model n) ℂ :=
  Matrix.conjTranspose (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) *
    (A.map n g : Matrix (A.model n) (A.model n) ℂ)

theorem normalizedMap_isUnitary (A : WeakMFApproximation G) (n : ℕ) (g : G) :
    normalizedMap A n g ∈ Matrix.unitaryGroup (A.model n) ℂ := by
  have hustar : Matrix.conjTranspose (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) ∈
      Matrix.unitaryGroup (A.model n) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem (A.map n 1).property
  exact mul_mem hustar (A.map n g).property

/-- **`V_n(1) = 1`, exactly.** -/
theorem normalizedMap_one (A : WeakMFApproximation G) (n : ℕ) :
    normalizedMap A n 1 = 1 := by
  have h := (A.map n 1).property
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
  exact h

theorem norm_normalizedMap_sub_one (A : WeakMFApproximation G) (n : ℕ) (g : G) :
    ‖normalizedMap A n g - 1‖ =
      ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n 1 : Matrix (A.model n) (A.model n) ℂ)‖ :=
  norm_conjTranspose_mul_sub_one (A.map n 1).property

theorem norm_normalizedMap_mul_sub_le (A : WeakMFApproximation G) (n : ℕ) (g h : G) :
    ‖normalizedMap A n (g * h) - normalizedMap A n g * normalizedMap A n h‖ ≤
      ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
            (A.map n h : Matrix (A.model n) (A.model n) ℂ)‖ +
      ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) *
            (A.map n 1 : Matrix (A.model n) (A.model n) ℂ)‖ :=
  norm_conjTranspose_mul_sub_conjTranspose_mul_mul_le
    (A.map n 1).property (A.map n g).property (A.map n h).property

end NormalizedMap

/-- **Forward direction, with `V_n(1) = 1` genuinely established.**  Every
countable MF group admits a sequential family of finite-dimensional unitary
models with `V_n(1) = 1` on the nose, multiplicative defect tending to `0` in
operator norm, and positive `limsup` separation of every nonidentity
element. -/
theorem exists_literalMFModel_of_isCDEOperatorMF (G : Type) [Group G] [Countable G]
    (hG : IsCDEOperatorMF G) :
    ∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ),
      (∀ n, 0 < Fintype.card (X n)) ∧
        (∀ n, V n 1 = 1) ∧
        (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
          ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
            (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
        (∀ g : G, g ≠ 1 → 0 < Filter.limsup
          (fun n ↦ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) Filter.atTop) := by
  obtain ⟨A⟩ := (isCDEOperatorMF_iff_nonempty_weakMFApproximation G).mp hG
  refine ⟨A.model, fun n g ↦ ⟨normalizedMap A n g, normalizedMap_isUnitary A n g⟩,
    A.modelNonempty, fun n ↦ Subtype.ext (normalizedMap_one A n), ?_, ?_⟩
  · intro g h ε hε
    obtain ⟨N1, hN1⟩ := A.asymptoticallyMultiplicative g h (ε / 2) (by linarith)
    obtain ⟨N2, hN2⟩ := A.asymptoticallyMultiplicative 1 1 (ε / 2) (by linarith)
    refine ⟨max N1 N2, fun n hn ↦ ?_⟩
    have h1 := hN1 n (le_trans (le_max_left N1 N2) hn)
    have h2 := hN2 n (le_trans (le_max_right N1 N2) hn)
    simp only [one_mul] at h2
    calc ‖normalizedMap A n (g * h) - normalizedMap A n g * normalizedMap A n h‖
        ≤ ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
              (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
                (A.map n h : Matrix (A.model n) (A.model n) ℂ)‖ +
            ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) -
              (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) *
                (A.map n 1 : Matrix (A.model n) (A.model n) ℂ)‖ :=
          norm_normalizedMap_mul_sub_le A n g h
      _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
      _ = ε := by ring
  · intro g hg
    obtain ⟨N, hN⟩ := A.separatedEventually g 1 hg
    have hev : ∀ᶠ n in Filter.atTop, A.separation ≤ ‖normalizedMap A n g - 1‖ := by
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      rw [norm_normalizedMap_sub_one A n g]
      exact hN n hn
    have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n ↦ ‖normalizedMap A n g - 1‖) := by
      refine Filter.isBoundedUnder_of ⟨2, fun n ↦ ?_⟩
      letI : Nonempty (A.model n) := Fintype.card_pos_iff.mp (A.modelNonempty n)
      have hv : ‖normalizedMap A n g‖ = 1 :=
        CStarRing.norm_of_mem_unitary (normalizedMap_isUnitary A n g)
      have hone : ‖(1 : Matrix (A.model n) (A.model n) ℂ)‖ = 1 := CStarRing.norm_one
      have htri := norm_sub_le (normalizedMap A n g) (1 : Matrix (A.model n) (A.model n) ℂ)
      rw [hv, hone] at htri
      linarith
    exact lt_of_lt_of_le A.separation_pos
      (Filter.le_limsup_of_frequently_le hev.frequently hbdd)

/-- **The Introduction's operator-norm MF definition, literally.**  A genuine
equivalence with `IsCDEOperatorMF`, including the `V_n(1) = 1` clause. -/
def PrintedMFDefinitionLiteral : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    IsCDEOperatorMF G ↔
      ∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ),
        (∀ n, 0 < Fintype.card (X n)) ∧
          (∀ n, V n 1 = 1) ∧
          (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
            ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
              (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
          (∀ g : G, g ≠ 1 → 0 < Filter.limsup
            (fun n ↦ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) Filter.atTop)

/-- Closed proof.  Forward is `exists_literalMFModel_of_isCDEOperatorMF`;
backward needs no `V_n(1) = 1` hypothesis at all and is exactly
`PrintedModelSeparationConverse.isCDEOperatorMF_of_limsup_separating_unitary_models`. -/
theorem manuscriptIntroductionMFDefinition : PrintedMFDefinitionLiteral := by
  intro G _ _
  constructor
  · exact exists_literalMFModel_of_isCDEOperatorMF G
  · rintro ⟨X, V, hX, -, hmul, hsep⟩
    exact isCDEOperatorMF_of_limsup_separating_unitary_models G X V hX hmul hsep

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
