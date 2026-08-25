import GroupApproximation.Analysis.CollapseUnitaryLift
import GroupApproximation.Manuscript.OneSidedMFRadical.LiteralMFClosure
import GroupApproximation.Sofic.NormMFUniversalCorona

/-!
# The printed diagonal construction in the MF-radical introduction

This file exposes the objects and estimates in sentences 31--37 of the
original proof of `prop:mf-residual-calculus`.  In the only degenerate case
omitted by the prose, the quotient has no nonidentity elements; the main
alternative below states that case explicitly.  In the nontrivial case the
sequence really consists of nonidentity elements and is onto that subtype.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

local instance introQuotientCountable {G : Type u} [Group G] [Countable G] :
    Countable (G ⧸ manuscriptCoronaMFResidual G) :=
  Function.Surjective.countable
    (QuotientGroup.mk'_surjective (manuscriptCoronaMFResidual G))

/-! ## Sentences 31 and 32: the two enumerations and their detectors -/

/-- The literal enumeration data used by the printed proof.  `element` has no
identity values and is onto the subtype of nonidentity elements; `pair` is
onto `Q × Q`. -/
structure IntroEnumerations (Q : Type u) [Group Q] where
  element : ℕ → Q
  element_ne_one : ∀ j, element j ≠ 1
  element_surjective : ∀ q : Q, q ≠ 1 → ∃ j, element j = q
  pair : ℕ → Q × Q
  pair_surjective : Function.Surjective pair

/-- **Sentence 31, with its necessary degenerate branch made explicit.**  A
countable group is trivial, or its nonidentity elements and all ordered pairs
admit the enumerations printed in the manuscript. -/
theorem manuscriptIntroEnumerateNonidentityAndPairs
    (Q : Type u) [Group Q] [Countable Q] :
    Subsingleton Q ∨ Nonempty (IntroEnumerations Q) := by
  classical
  by_cases hQ : Nontrivial Q
  · right
    letI : Nontrivial Q := hQ
    let Qne := {q : Q // q ≠ 1}
    haveI : Nonempty Qne := by
      obtain ⟨q, hq⟩ := exists_ne (1 : Q)
      exact ⟨⟨q, hq⟩⟩
    obtain ⟨e, he⟩ := exists_surjective_nat Qne
    obtain ⟨p, hp⟩ := exists_surjective_nat (Q × Q)
    refine ⟨{
      element := fun j ↦ (e j : Q)
      element_ne_one := fun j ↦ (e j).property
      element_surjective := ?_
      pair := p
      pair_surjective := hp }⟩
    intro q hq
    obtain ⟨j, hj⟩ := he ⟨q, hq⟩
    exact ⟨j, congrArg Subtype.val hj⟩
  · left
    exact not_nontrivial_iff_subsingleton.mp hQ

/-- A simultaneous family of the objects printed after the enumerations:
one corona detector for every `x_j`, a positive separation, and a sequential
unitary almost representation retaining that separation.  The detector may be
the same faithful corona representation for every `j`; its marked value is
nevertheless exposed separately for every index. -/
structure IntroDetectorFamily (Q : Type u) [Group Q] where
  enumeration : IntroEnumerations Q
  model : ℕ → FiniteModel
  model_pos : ∀ n, 0 < Fintype.card (model n)
  detector : Q →* NormMatrixCoronaUnitary model
  detector_injective : Function.Injective detector
  detector_marks_nontrivial : ∀ j, detector (enumeration.element j) ≠ 1
  coordinateModel : ∀ j,
    MarkedOpAlmostRepresentation Q (enumeration.element j)

/-- **Sentence 32 in the sequence-corona presentation.**  In the nontrivial
case each enumerated nonidentity element has a corona detector and a strictly
positive operator-norm separation parameter. -/
theorem manuscriptIntroCoronaDetectorPerNonidentity
    (Q : Type u) [Group Q] [Countable Q] (hMF : IsOperatorMF Q)
    (E : IntroEnumerations Q) : Nonempty (IntroDetectorFamily Q) := by
  classical
  obtain ⟨X, hX, rho, hrho⟩ := hMF
  have hmark (j : ℕ) : rho (E.element j) ≠ 1 := by
    intro hj
    exact E.element_ne_one j (hrho (by simpa using hj))
  let A : ∀ j, MarkedOpAlmostRepresentation Q (E.element j) :=
    fun j ↦ Classical.choice
      (exists_markedOpAlmostRepresentation_of_normMatrixCorona_ne_one
        X rho (hmark j))
  exact ⟨{
    enumeration := E
    model := X
    model_pos := hX
    detector := rho
    detector_injective := hrho
    detector_marks_nontrivial := hmark
    coordinateModel := A }⟩

/-- The manuscript's phrase "positive distance from the identity", literally
in a genuine norm-matrix C-star corona.  One faithful representation detects
all the enumerated elements; `gap j` is its actual C-star norm distance. -/
theorem manuscriptIntroPositiveCoronaNormDistance
    (Q : Type u) [Group Q] [Countable Q] (E : IntroEnumerations Q)
    (hMF : IsCDEOperatorMF Q) :
    ∃ (d : ℕ → ℕ), ∃ hd : ∀ n, 0 < d n,
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      ∃ rho : Q →* unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))),
        Function.Injective rho ∧
          ∀ j, 0 < ‖(rho (E.element j) :
            NormMatrixCStarCorona (fun n ↦ naturalFiniteModel (d n))) - 1‖ := by
  obtain ⟨d, hd, _hmono, rho, hrho⟩ := hMF
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
    fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
  refine ⟨d, hd, ?_⟩
  refine ⟨rho, hrho, ?_⟩
  intro j
  apply norm_pos_iff.mpr
  intro hzero
  have hval :
      (rho (E.element j) :
        NormMatrixCStarCorona (fun n ↦ naturalFiniteModel (d n))) = 1 :=
    sub_eq_zero.mp hzero
  apply E.element_ne_one j
  apply hrho
  apply Subtype.ext
  simpa using hval

/-! ## Sentence 33: every detector descends through the radical quotient -/

/-- **Sentence 33.**  Every genuine-corona homomorphism kills the MF radical
and therefore factors uniquely through `G / Rad_MF(G)`.  The arbitrary
detector and the factorization equation both occur in the statement. -/
theorem manuscriptIntroEveryDetectorDescends
    (G : Type u) [Group G] [Countable G]
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) :
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    ∀ rho : G →* unitary (NormMatrixCStarCorona
        (fun n ↦ naturalFiniteModel (d n))),
      ∃! rhoBar : (G ⧸ manuscriptCoronaMFResidual G) →*
          unitary (NormMatrixCStarCorona
            (fun n ↦ naturalFiniteModel (d n))),
        rhoBar.comp (QuotientGroup.mk' (manuscriptCoronaMFResidual G)) = rho := by
  intro rho
  exact existsUnique_quotient_factorization_to_manuscriptCorona
    (manuscriptCoronaMFResidual G) le_rfl d hd rho

/-! ## Sentence 34: coordinate unitary lifts and vanishing defects -/

set_option maxHeartbeats 800000 in
/-- **Sentence 34.**  An arbitrary homomorphism into a genuine corona has
coordinatewise unitary lifts representing every value, and every fixed
multiplication defect of those lifts tends to zero. -/
theorem manuscriptIntroCoordinateUnitaryLifts
    (Q : Type u) [Group Q] (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)]
    (rho : Q →* unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
    ∃ lift : Q → ∀ n, Matrix.unitaryGroup (X n) ℂ,
      (∀ q, unitarySequenceToCorona X (lift q) = rho q) ∧
      ∀ q r,
        Tendsto (fun n ↦
          ‖((lift (q * r) n : Matrix (X n) (X n) ℂ)) -
            (lift q n : Matrix (X n) (X n) ℂ) * lift r n‖)
          cofinite (nhds 0) := by
  classical
  choose lift hlift using fun q : Q ↦
    CollapseUnitaryLift.unitarySequenceToCorona_surjective X (rho q)
  refine ⟨lift, hlift, ?_⟩
  intro q r
  have hclass :
      unitarySequenceToCorona X (lift (q * r)) =
        unitarySequenceToCorona X (lift q * lift r) := by
    calc
      unitarySequenceToCorona X (lift (q * r)) = rho (q * r) := hlift (q * r)
      _ = rho q * rho r := map_mul rho q r
      _ = unitarySequenceToCorona X (lift q) *
          unitarySequenceToCorona X (lift r) := by rw [hlift q, hlift r]
      _ = unitarySequenceToCorona X (lift q * lift r) :=
        (map_mul (unitarySequenceToCorona X) _ _).symm
  have hzero : normMatrixCStarCoronaMk (fun n ↦ X n)
      (unitarySequenceBounded X (lift (q * r)) -
        unitarySequenceBounded X (lift q * lift r)) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrArg
      (fun t : unitary (NormMatrixCStarCorona (fun n ↦ X n)) ↦
        (t : NormMatrixCStarCorona (fun n ↦ X n))) hclass
  have hnull : IsNullMatrixSequence (fun n ↦ X n) cofinite
      (unitarySequenceBounded X (lift (q * r)) -
        unitarySequenceBounded X (lift q * lift r)) :=
    (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mp hzero
  change Tendsto (fun n ↦
      ‖((lift (q * r) n : Matrix (X n) (X n) ℂ)) -
        (lift q n : Matrix (X n) (X n) ℂ) * lift r n‖)
    cofinite (nhds 0) at hnull
  exact hnull

/-! ## Sentences 35 and 36: finite diagonal stages -/

/-- The coordinate selected from each of the first `n` marked models.  Its
fields are exactly the two simultaneous requirements in the printed proof,
plus "far enough out" as the explicit inequality `n ≤ coordinate i`. -/
structure IntroFiniteStage {Q : Type u} [Group Q]
    (D : IntroDetectorFamily Q) (n : ℕ) where
  coordinate : ℕ → ℕ
  far : ∀ i, i < n → n ≤ coordinate i
  multiplication_defect : ∀ i, i < n → ∀ r, r < n →
    ‖((D.coordinateModel i).map (coordinate i)
          ((D.enumeration.pair r).1 * (D.enumeration.pair r).2) :
        Matrix ((D.coordinateModel i).model (coordinate i))
          ((D.coordinateModel i).model (coordinate i)) ℂ) -
      (D.coordinateModel i).map (coordinate i) (D.enumeration.pair r).1 *
        (D.coordinateModel i).map (coordinate i) (D.enumeration.pair r).2‖
      ≤ 1 / (n : ℝ)
  half_separation : ∀ i, i < n →
    (D.coordinateModel i).separation / 2 ≤
      ‖((D.coordinateModel i).map (coordinate i)
          (D.enumeration.element i) :
        Matrix ((D.coordinateModel i).model (coordinate i))
          ((D.coordinateModel i).model (coordinate i)) ℂ) -
        (D.coordinateModel i).map (coordinate i) 1‖

/-- **The simultaneous finite-stage choice in sentence 35.**  At every
positive stage, one can take one sufficiently late coordinate from each of
the first `n` marked models so that the first `n` enumerated multiplication
defects are at most `1/n` and every marked value retains at least half its
separation. -/
theorem manuscriptIntroExistsFiniteDiagonalStage
    {Q : Type u} [Group Q] (D : IntroDetectorFamily Q)
    (n : ℕ) (hn : 0 < n) : Nonempty (IntroFiniteStage D n) := by
  classical
  let P : Finset (ℕ × ℕ) := Finset.range n ×ˢ Finset.range n
  have htolerance : 0 < (1 / (n : ℝ)) := by positivity
  have hev : ∀ᶠ k in atTop, ∀ p ∈ P,
      ‖((D.coordinateModel p.1).map k
            ((D.enumeration.pair p.2).1 * (D.enumeration.pair p.2).2) :
          Matrix ((D.coordinateModel p.1).model k)
            ((D.coordinateModel p.1).model k) ℂ) -
        (D.coordinateModel p.1).map k (D.enumeration.pair p.2).1 *
          (D.coordinateModel p.1).map k (D.enumeration.pair p.2).2‖
        ≤ 1 / (n : ℝ) := by
    rw [eventually_all_finset]
    intro p hp
    obtain ⟨Np, hNp⟩ :=
      (D.coordinateModel p.1).asymptoticallyMultiplicative
        (D.enumeration.pair p.2).1 (D.enumeration.pair p.2).2
        (1 / (n : ℝ)) htolerance
    rw [eventually_atTop]
    exact ⟨Np, hNp⟩
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  let stage : ℕ → ℕ := fun _ ↦ max n N
  refine ⟨{
    coordinate := stage
    far := fun _ _ ↦ le_max_left n N
    multiplication_defect := ?_
    half_separation := ?_ }⟩
  · intro i hi r hr
    exact hN (max n N) (le_max_right n N) (i, r)
      (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi,
        Finset.mem_range.mpr hr⟩)
  · intro i hi
    have hsep := (D.coordinateModel i).marked_separated (stage i)
    have hpos := (D.coordinateModel i).separation_pos
    exact (by linarith : (D.coordinateModel i).separation / 2 ≤
      (D.coordinateModel i).separation).trans hsep

/-- The block list that literally takes one selected coordinate from each of
the first `n` models. -/
def introDiagonalBlocks {Q : Type u} [Group Q]
    (D : IntroDetectorFamily Q) {n : ℕ} (S : IntroFiniteStage D n) :
    List (UnitaryBlock Q) :=
  (List.range n).map fun i ↦ {
    model := (D.coordinateModel i).model (S.coordinate i)
    map := fun q ↦ (D.coordinateModel i).map (S.coordinate i) q }

/-- The direct sum of the selected coordinates has each of the first `n`
printed multiplication defects at most `1/n`. -/
theorem manuscriptIntroDiagonalSumDefect
    {Q : Type u} [Group Q] (D : IntroDetectorFamily Q)
    {n : ℕ} (hn : 0 < n) (S : IntroFiniteStage D n)
    (r : ℕ) (hr : r < n) :
    ‖blockListMap (introDiagonalBlocks D S)
          ((D.enumeration.pair r).1 * (D.enumeration.pair r).2) -
        blockListMap (introDiagonalBlocks D S) (D.enumeration.pair r).1 *
          blockListMap (introDiagonalBlocks D S) (D.enumeration.pair r).2‖
      ≤ 1 / (n : ℝ) := by
  classical
  apply norm_blockListMap_mul_sub_le Q _ _ _ (by positivity)
  intro B hB
  rw [introDiagonalBlocks, List.mem_map] at hB
  obtain ⟨i, hi, rfl⟩ := hB
  exact S.multiplication_defect i (by simpa using hi) r hr

/-- Every one of the first `n` designated elements keeps half of its own
separation in the direct sum, through its selected block. -/
theorem manuscriptIntroDiagonalSumHalfSeparation
    {Q : Type u} [Group Q] (D : IntroDetectorFamily Q)
    {n : ℕ} (S : IntroFiniteStage D n)
    (i : ℕ) (hi : i < n) :
    (D.coordinateModel i).separation / 2 ≤
      ‖blockListMap (introDiagonalBlocks D S) (D.enumeration.element i) -
        blockListMap (introDiagonalBlocks D S) 1‖ := by
  classical
  have hmem :
      ({ model := (D.coordinateModel i).model (S.coordinate i)
         map := fun q ↦ (D.coordinateModel i).map (S.coordinate i) q } :
        UnitaryBlock Q) ∈ introDiagonalBlocks D S := by
    rw [introDiagonalBlocks]
    exact List.mem_map_of_mem (by simpa using hi)
  exact (S.half_separation i hi).trans
    (norm_blockListMap_sub_ge_of_mem hmem (D.enumeration.element i) 1)

/-- **"Arbitrarily far out" in sentence 36.**  A frequently retained marked
gap can be intersected with finitely many eventual defect bounds and an
arbitrary tail. -/
theorem manuscriptIntroArbitrarilyFarCoordinate
    {Q : Type u} [Group Q] (X : ℕ → FiniteModel)
    (rho : Q →* NormMatrixCoronaUnitary X)
    (lift : Q → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hlift : ∀ q, QuotientGroup.mk (lift q) = rho q)
    {z : Q} (hz : rho z ≠ 1) (T : Finset (Q × Q))
    (N : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ k ≥ N,
      delta ≤ ‖(lift z k : Matrix (X k) (X k) ℂ) - lift 1 k‖ ∧
      ∀ p ∈ T,
        ‖(lift (p.1 * p.2) k : Matrix (X k) (X k) ℂ) -
          (lift p.1 k : Matrix (X k) (X k) ℂ) * lift p.2 k‖
          ≤ epsilon := by
  obtain ⟨delta, hdelta, hfreq⟩ :=
    normMatrixCorona_lift_frequently_marked_separated X rho lift hlift hz
  have hmul : ∀ᶠ k in cofinite, ∀ p ∈ T,
      ‖(lift (p.1 * p.2) k : Matrix (X k) (X k) ℂ) -
        (lift p.1 k : Matrix (X k) (X k) ℂ) * lift p.2 k‖
        ≤ epsilon := by
    rw [eventually_all_finset]
    intro p hp
    exact normMatrixCorona_lift_eventually_multiplicative X rho lift hlift
      p.1 p.2 epsilon hepsilon
  have hfrequent := hfreq.and_eventually hmul
  rw [Nat.cofinite_eq_atTop, frequently_atTop] at hfrequent
  obtain ⟨k, hkN, hksep, hkmul⟩ := hfrequent N
  exact ⟨delta, hdelta, k, hkN, hksep, hkmul⟩

/-- The second analytic clause of sentence 36, stated without abbreviation:
the norm of a corona class is the limsup of its coordinate operator norms. -/
theorem manuscriptIntroQuotientNormIsLimsup
    (X : ℕ → Type u) [∀ n, Fintype (X n)]
    [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]
    (a : BoundedMatrixSequence X) :
    ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X cofinite) a‖ =
      Filter.limsup (fun n ↦ ‖a n‖) cofinite :=
  norm_filterMatrixCorona_mk_eq_limsup X cofinite a

/-! ## Sentence 37: the assembled faithful quotient model -/

/-- The chosen positive stage numbered `n+1`. -/
def introChosenFiniteStage {Q : Type u} [Group Q]
    (D : IntroDetectorFamily Q) (n : ℕ) : IntroFiniteStage D (n + 1) :=
  Classical.choice
    (manuscriptIntroExistsFiniteDiagonalStage D (n + 1) (Nat.succ_pos n))

/-- The model at stage `n` of the printed diagonal sum. -/
def introDiagonalModel {Q : Type u} [Group Q]
    (D : IntroDetectorFamily Q) (n : ℕ) : FiniteModel :=
  blockListModel (introDiagonalBlocks D (introChosenFiniteStage D n))

/-- The unitary block diagonal at stage `n`. -/
def introDiagonalMap {Q : Type u} [Group Q]
    (D : IntroDetectorFamily Q) (n : ℕ) (q : Q) :
    Matrix.unitaryGroup (introDiagonalModel D n) ℂ :=
  blockListUnitary
    (introDiagonalBlocks D (introChosenFiniteStage D n)) q

/-- The finite diagonal sums form an operator-norm almost representation.
The proof uses the explicit pair enumeration and the `1/(n+1)` estimate of
`manuscriptIntroDiagonalSumDefect`. -/
def introDiagonalAlmostRepresentation {Q : Type u} [Group Q]
    (D : IntroDetectorFamily Q) : OpAlmostRepresentation Q where
  model := introDiagonalModel D
  modelNonempty n := by
    let S := introChosenFiniteStage D n
    let B : UnitaryBlock Q := {
      model := (D.coordinateModel 0).model (S.coordinate 0)
      map := fun q ↦ (D.coordinateModel 0).map (S.coordinate 0) q }
    have hB : B ∈ introDiagonalBlocks D S := by
      rw [introDiagonalBlocks]
      exact List.mem_map_of_mem (by simp)
    exact card_blockListModel_pos_of_mem hB
      ((D.coordinateModel 0).modelNonempty (S.coordinate 0))
  map := introDiagonalMap D
  asymptoticallyMultiplicative := by
    intro g h epsilon hepsilon
    obtain ⟨r, hr⟩ := D.enumeration.pair_surjective (g, h)
    obtain ⟨Ne, hNe⟩ := exists_nat_gt (1 / epsilon)
    refine ⟨max r Ne, fun n hn ↦ ?_⟩
    have hrn : r < n + 1 := by
      have : r ≤ n := (le_max_left r Ne).trans hn
      omega
    have hsmall : 1 / ((n + 1 : ℕ) : ℝ) ≤ epsilon := by
      have hNen : (Ne : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_max_right r Ne).trans hn
      have hlt : (1 : ℝ) / epsilon < (n : ℝ) + 1 := by
        exact hNe.trans_le (by linarith)
      rw [Nat.cast_add, Nat.cast_one]
      apply (div_le_iff₀ (by positivity)).2
      rw [div_lt_iff₀ hepsilon] at hlt
      nlinarith
    change
      ‖blockListMap
            (introDiagonalBlocks D (introChosenFiniteStage D n)) (g * h) -
          blockListMap
              (introDiagonalBlocks D (introChosenFiniteStage D n)) g *
            blockListMap
              (introDiagonalBlocks D (introChosenFiniteStage D n)) h‖
        ≤ epsilon
    have hdef := manuscriptIntroDiagonalSumDefect D (Nat.succ_pos n)
      (introChosenFiniteStage D n) r hrn
    rw [hr] at hdef
    exact hdef.trans hsmall

/-- Every enumerated nonidentity element remains separated at every diagonal
stage from the point at which its block is included. -/
theorem manuscriptIntroDiagonalEventuallySeparates
    {Q : Type u} [Group Q] (D : IntroDetectorFamily Q) (i n : ℕ)
    (hin : i ≤ n) :
    (D.coordinateModel i).separation / 2 ≤
      opLength (introDiagonalModel D n)
        ((introDiagonalMap D n 1)⁻¹ *
          introDiagonalMap D n (D.enumeration.element i)) := by
  have hi : i < n + 1 := by omega
  rw [opLength_inv_mul]
  exact manuscriptIntroDiagonalSumHalfSeparation D
    (introChosenFiniteStage D n) i hi

/-- The corona homomorphism represented by the printed diagonal sums. -/
def introDiagonalCoronaHom {Q : Type u} [Group Q]
    (D : IntroDetectorFamily Q) :
    Q →* NormMatrixCoronaUnitary (introDiagonalModel D) := by
  let A := introDiagonalAlmostRepresentation D
  have hnull : ∀ g h : Q,
      (fun n ↦ A.map n g * A.map n h)⁻¹ *
          (fun n ↦ A.map n (g * h)) ∈
        nullCofiniteOpSubgroup A.model := by
    intro g h epsilon hepsilon
    obtain ⟨N, hN⟩ :=
      A.asymptoticallyMultiplicative g h (epsilon / 2) (by linarith)
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with n hn
    change opLength (A.model n)
      ((A.map n g * A.map n h)⁻¹ * A.map n (g * h)) < epsilon
    rw [opLength_inv_mul]
    exact (hN n hn).trans_lt (by linarith)
  exact MonoidHom.mk' (fun g ↦ QuotientGroup.mk (fun n ↦ A.map n g))
    (fun g h ↦ by
      rw [← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq.mpr (hnull g h)).symm)

/-- The homomorphism represented by the printed diagonal sums is faithful.
The proof uses surjectivity of the nonidentity enumeration and the retained
half-separation block, rather than invoking an independently constructed MF
embedding. -/
theorem introDiagonalCoronaHom_injective
    {Q : Type u} [Group Q] (D : IntroDetectorFamily Q) :
    Function.Injective (introDiagonalCoronaHom D) := by
  intro g h hgh
  by_contra hne
  have hz : h⁻¹ * g ≠ 1 := by
    intro hz
    apply hne
    calc
      g = h * (h⁻¹ * g) := by group
      _ = h := by rw [hz, mul_one]
  obtain ⟨i, hi⟩ := D.enumeration.element_surjective (h⁻¹ * g) hz
  have hrho :
      introDiagonalCoronaHom D (h⁻¹ * g) =
        introDiagonalCoronaHom D 1 := by
    rw [map_mul, map_inv, hgh, inv_mul_cancel, map_one]
  have hmem :
      (fun n ↦ (introDiagonalAlmostRepresentation D).map n 1)⁻¹ *
          (fun n ↦
            (introDiagonalAlmostRepresentation D).map n (h⁻¹ * g)) ∈
        nullCofiniteOpSubgroup (introDiagonalModel D) :=
    QuotientGroup.eq.mp hrho.symm
  have hclose := hmem
    ((D.coordinateModel i).separation / 2)
    (half_pos (D.coordinateModel i).separation_pos)
  have htail : ∀ᶠ n in cofinite, i ≤ n := by
    rw [Nat.cofinite_eq_atTop]
    exact eventually_ge_atTop i
  obtain ⟨n, hin, hnclose⟩ := (htail.and hclose).exists
  have hfar := manuscriptIntroDiagonalEventuallySeparates D i n hin
  change opLength (introDiagonalModel D n)
      ((introDiagonalMap D n 1)⁻¹ * introDiagonalMap D n (h⁻¹ * g)) <
      (D.coordinateModel i).separation / 2 at hnclose
  have hnclose' : opLength (introDiagonalModel D n)
      ((introDiagonalMap D n 1)⁻¹ *
        introDiagonalMap D n (D.enumeration.element i)) <
      (D.coordinateModel i).separation / 2 := by
    simpa only [hi] using hnclose
  exact (not_lt_of_ge hfar) hnclose'

/-- In the nontrivial branch, all printed preliminary data exist for the
universal MF quotient.  In the trivial branch there is nothing to enumerate. -/
theorem manuscriptIntroUniversalQuotientDiagonalAlternative
    (G : Type u) [Group G] [Countable G] :
    let Q := G ⧸ manuscriptCoronaMFResidual G
    Subsingleton Q ∨ Nonempty (IntroDetectorFamily Q) := by
  let Q := G ⧸ manuscriptCoronaMFResidual G
  rcases manuscriptIntroEnumerateNonidentityAndPairs Q with htriv | hE
  · exact Or.inl htriv
  · right
    obtain ⟨E⟩ := hE
    exact manuscriptIntroCoronaDetectorPerNonidentity Q
      ((isCDEOperatorMF_iff_isOperatorMF Q).mp
        manuscriptCoronaMFQuotient_isCDEOperatorMF) E

/-- **Sentence 37.**  The diagonal construction has the advertised endpoint:
the corona representation of `G / Rad_MF(G)` is faithful, hence the quotient
is MF.  The two clauses expose both the faithful corona map and the named MF
predicate. -/
theorem manuscriptIntroDiagonalRepresentationFaithful
    (G : Type u) [Group G] [Countable G] :
    let Q := G ⧸ manuscriptCoronaMFResidual G
    (∃ X : ℕ → FiniteModel, (∀ n, 0 < Fintype.card (X n)) ∧
      ∃ rho : Q →* NormMatrixCoronaUnitary X, Function.Injective rho) ∧
      IsCDEOperatorMF Q := by
  let Q := G ⧸ manuscriptCoronaMFResidual G
  rcases manuscriptIntroEnumerateNonidentityAndPairs Q with htriv | hE
  · let X : ℕ → FiniteModel := fun _ ↦
      ⟨PUnit, inferInstance, inferInstance⟩
    let rho : Q →* NormMatrixCoronaUnitary X := 1
    have hrho : Function.Injective rho := by
      intro q r _
      exact Subsingleton.elim q r
    have hop : IsOperatorMF Q := ⟨X, (by simp [X]), rho, hrho⟩
    exact ⟨hop, (isCDEOperatorMF_iff_isOperatorMF Q).mpr hop⟩
  · obtain ⟨E⟩ := hE
    obtain ⟨D⟩ := manuscriptIntroCoronaDetectorPerNonidentity Q
      ((isCDEOperatorMF_iff_isOperatorMF Q).mp
        manuscriptCoronaMFQuotient_isCDEOperatorMF) E
    have hop : IsOperatorMF Q :=
      ⟨introDiagonalModel D,
        fun n ↦ by
          exact (introDiagonalAlmostRepresentation D).modelNonempty n,
        introDiagonalCoronaHom D,
        introDiagonalCoronaHom_injective D⟩
    exact ⟨hop, (isCDEOperatorMF_iff_isOperatorMF Q).mpr hop⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
