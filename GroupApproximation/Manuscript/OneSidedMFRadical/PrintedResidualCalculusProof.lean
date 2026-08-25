import GroupApproximation.Manuscript.OneSidedMFRadical.ResidualCalculus
import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import GroupApproximation.Sofic.NormMFUniversalCorona

/-!
# The printed proof of `prop:mf-residual-calculus`, sentence by sentence

`non_mf_groups_exist.tex`, the proof of
`\begin{proposition}[basic properties of the MF radical]`
`\label{prop:mf-residual-calculus}`.  The manuscript is under revision, so this
module is anchored on the label, not on line numbers.

`Manuscript/OneSidedMFRadical/ResidualCalculus.lean` already carries the
*statement* of the proposition as one closed `Prop`
(`MFResidualCalculus`).  Its printed *proof*, however, runs through ten
sentences — normality of an intersection of kernels, full invariance through
`π ∘ α`, two enumerations, a corona detector for each nonidentity class,
descent of every detector to the quotient, polar-correction coordinate lifts,
a stagewise direct sum, the "arbitrarily far out" selection, faithfulness on
`G/R`, and the transfer of the whole argument to `G/N` — and none of those
sentences had a named Lean declaration a referee could check against.

The mathematics is already in the tree.  `Sofic/NormMFUniversalCorona.lean`
carries the diagonalization (`blockDiagMatrix`, `l2_opNorm_blockDiag`,
`blockListMap`, `norm_blockListMap_mul_sub_le`,
`norm_blockListMap_sub_ge_of_mem`, `isOperatorMF_of_normMFResidual_eq_bot`);
`Sofic/ActualCoronaMFRadical.lean` carries the radical, its functoriality, the
single faithful corona representation and the descent lemma;
`Analysis/NormMatrixCoronaUnitary.lean` carries the polar correction; and
`Sofic/MFRelationClosure.lean` carries the closure criterion.  Nothing here
redoes that work: each printed sentence is restated as a named `Prop` whose
quantifiers and hypotheses live *inside* the statement — the only shape
`#audit_closed_axioms` accepts, since the macro throws on any leading binder —
and is proved from the existing declarations.

## Where the Lean statements differ from the printed sentences

Three deliberate deviations, all in the direction of a *stronger* or *more
explicit* claim, are recorded in the individual docstrings and repeated here:

* Sentence 6 cites `Lemma~\ref{lem:central-corona-corner}`.  That lemma is the
  *central corona corner* statement (compressing a corona representation by a
  commuting projection).  The printed sentence uses only its polar-correction
  step, i.e. the case of the trivial corner, and that is what
  `PrintedPolarCoordinateUnitaryLifts` states: every unitary of the corona has
  a coordinatewise-unitary representative.  The corner statement itself is not
  restated here.
* Sentence 7 says the designated value "retains at least half of its
  corona-norm separation".  The block-sum estimate in the tree is sharper and
  differently anchored: the operator norm of a block diagonal is the maximum of
  the block norms, so the block sum retains the *whole* separation of the
  designated coordinate.  Both the full retention and the printed half are
  stated.  The constant retained is the coordinate separation of the chosen
  block, not literally half of a corona norm; the arithmetic relation between
  the two is not asserted.
* Sentence 7 says "the first `n` multiplication defects are at most `1/n`".
  The tree's estimate holds for an arbitrary nonnegative tolerance; the printed
  `1/n` is stated as the instance actually printed.

No theorem from the literature is an input.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The quotient of a countable group is countable.  The same local instance
carries the corresponding statements in `Sofic/ActualCoronaMFRadical.lean` and
`Manuscript/OneSidedMFRadical/PrintedFullKernelPullback.lean`. -/
local instance quotientGroupCountable {G : Type*} [Group G] (N : Subgroup G)
    [hN : N.Normal] [Countable G] :
    Countable (G ⧸ N) :=
  Function.Surjective.countable (@QuotientGroup.mk'_surjective G _ N hN)

/-! ## Sentence 1 -/

/-- **"An intersection of kernels is normal."**  The MF radical is literally
the intersection of the kernels of all genuine norm-matrix C-star-corona
representations, and that subgroup is normal. -/
def PrintedIntersectionOfKernelsIsNormal : Prop :=
  ∀ (G : Type) [Group G],
    (∀ x : G, x ∈ actualCoronaMFResidual G ↔
        ∀ (X : ℕ → FiniteModel), ∀ hX : ∀ n, 0 < Fintype.card (X n),
          letI : ∀ n, Nonempty (X n) :=
            fun n ↦ Fintype.card_pos_iff.mp (hX n)
          ∀ rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
            x ∈ rho.ker) ∧
      (actualCoronaMFResidual G).Normal

/-- Closed proof of the first printed sentence. -/
theorem manuscriptPrintedIntersectionOfKernelsIsNormal :
    PrintedIntersectionOfKernelsIsNormal := by
  intro G _
  refine ⟨fun x ↦ ⟨?_, ?_⟩, actualCoronaMFResidual_normal⟩
  · intro hx X hX
    letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
    intro rho
    exact MonoidHom.mem_ker.mpr (hx X hX rho)
  · intro hx X hX
    letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
    intro rho
    exact MonoidHom.mem_ker.mp (hx X hX rho)

/-! ## Sentence 2 -/

/-- **"If `α` is an endomorphism of `G`, `x ∈ Rad_MF(G)`, and `π` is a corona
homomorphism of `G`, then `π ∘ α` kills `x`.  Hence `π(α(x)) = 1` for every
`π`, which proves full invariance."**  Both halves are stated: the composite
`π ∘ α` is itself a corona homomorphism of `G`, so it kills `x`; and the
resulting statement `π(α(x)) = 1` for every `π` is exactly full invariance of
the radical. -/
def PrintedFullInvarianceThroughComposition : Prop :=
  ∀ (G : Type) [Group G],
    (∀ (alpha : G →* G) (x : G), x ∈ actualCoronaMFResidual G →
        ∀ (X : ℕ → FiniteModel), ∀ hX : ∀ n, 0 < Fintype.card (X n),
          letI : ∀ n, Nonempty (X n) :=
            fun n ↦ Fintype.card_pos_iff.mp (hX n)
          ∀ pi : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
            (pi.comp alpha) x = 1 ∧ pi (alpha x) = 1) ∧
      RadicalFunctoriality.IsFullyInvariant (actualCoronaMFResidual G)

/-- Closed proof of the second printed sentence. -/
theorem manuscriptPrintedFullInvarianceThroughComposition :
    PrintedFullInvarianceThroughComposition := by
  intro G _
  refine ⟨?_, fun f ↦ map_actualCoronaMFResidual_le f⟩
  intro alpha x hx X hX
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro pi
  exact ⟨hx X hX (pi.comp alpha), hx X hX (pi.comp alpha)⟩

/-! ## Sentence 3 -/

/-- **"Put `R = Rad_MF(G)` and enumerate the nonidentity elements of `G/R` as
`(x_j)_{j≥1}`, and enumerate the pairs in `(G/R)²`."**  Both enumerations
exist for a countable `G`.  The first is stated under the hypothesis that
`G/R` actually has a nonidentity element: that is the only case in which the
printed enumeration is used, and without it the family `(x_j)` would have to
be an enumeration of an empty type.  The enumeration of pairs needs no
hypothesis. -/
def PrintedEnumerationsOfTheQuotient : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    ((∃ y : G ⧸ actualCoronaMFResidual G, y ≠ 1) →
        ∃ mark : ℕ → {y : G ⧸ actualCoronaMFResidual G // y ≠ 1},
          Function.Surjective mark) ∧
      (∃ pair : ℕ →
          (G ⧸ actualCoronaMFResidual G) × (G ⧸ actualCoronaMFResidual G),
        Function.Surjective pair)

/-- Closed proof of the third printed sentence. -/
theorem manuscriptPrintedEnumerationsOfTheQuotient :
    PrintedEnumerationsOfTheQuotient := by
  intro G _ _
  constructor
  · rintro ⟨y, hy⟩
    haveI : Nonempty {y : G ⧸ actualCoronaMFResidual G // y ≠ 1} := ⟨⟨y, hy⟩⟩
    exact exists_surjective_nat {y : G ⧸ actualCoronaMFResidual G // y ≠ 1}
  · haveI : Nonempty
        ((G ⧸ actualCoronaMFResidual G) × (G ⧸ actualCoronaMFResidual G)) :=
      ⟨(1, 1)⟩
    exact exists_surjective_nat
      ((G ⧸ actualCoronaMFResidual G) × (G ⧸ actualCoronaMFResidual G))

/-! ## Sentence 4 -/

/-- **"For each `x_j`, the definition of `R` supplies a corona homomorphism
whose value at `x_j` has positive distance from the identity."**  The
hypothesis "`x_j` is a nonidentity element of `G/R`" is spelled on
representatives, as `x ∉ Rad_MF(G)`; the conclusion is the literal metric one,
`0 < ‖π(x) - 1‖` in the corona. -/
def PrintedCoronaDetectorAtEachMarkedClass : Prop :=
  ∀ (G : Type) [Group G] (x : G), x ∉ actualCoronaMFResidual G →
    ∃ (X : ℕ → FiniteModel), ∃ hX : ∀ n, 0 < Fintype.card (X n),
      letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
      ∃ pi : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
        0 < ‖(pi x : NormMatrixCStarCorona (fun n ↦ X n)) - 1‖

/-- Closed proof of the fourth printed sentence. -/
theorem manuscriptPrintedCoronaDetectorAtEachMarkedClass :
    PrintedCoronaDetectorAtEachMarkedClass := by
  intro G _ x hx
  by_contra hcon
  refine hx ?_
  intro X hX
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro pi
  by_contra hpi
  refine hcon ⟨X, hX, pi, norm_sub_pos_iff.mpr ?_⟩
  intro hval
  exact hpi (Subtype.ext hval)

/-! ## Sentence 5 -/

/-- **"Every such homomorphism kills `R` and therefore descends to
`G/R`."**  The radical is contained in the kernel of every corona
homomorphism, and the induced homomorphism on `G/R` is the unique one
compatible with the quotient map. -/
def PrintedDetectorKillsRadicalAndDescends : Prop :=
  ∀ (G : Type) [Group G] (X : ℕ → FiniteModel)
      (hX : ∀ n, 0 < Fintype.card (X n)),
    letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ pi : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      actualCoronaMFResidual G ≤ pi.ker ∧
        ∃! piBar : (G ⧸ actualCoronaMFResidual G) →*
            unitary (NormMatrixCStarCorona (fun n ↦ X n)),
          piBar.comp (QuotientGroup.mk' (actualCoronaMFResidual G)) = pi

/-- Closed proof of the fifth printed sentence. -/
theorem manuscriptPrintedDetectorKillsRadicalAndDescends :
    PrintedDetectorKillsRadicalAndDescends := by
  intro G _ X hX
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro pi
  refine ⟨fun y hy ↦ MonoidHom.mem_ker.mpr (hy X hX pi), ?_⟩
  exact existsUnique_quotient_factorization_to_actualCorona
    (actualCoronaMFResidual G) le_rfl X hX pi

/-! ## Sentence 6 -/

/-- **"Choose coordinate unitary lifts, using polar correction as in
Lemma~\ref{lem:central-corona-corner}."**  Every unitary of the genuine
norm-matrix C-star corona is the class of a coordinatewise-unitary sequence:
polar-correct the representative wherever its Gram defect is at most `1/2`,
and use the identity in the finitely many remaining coordinates.

This carries only the polar-correction step of the cited lemma — the case of
the trivial corner.  The corner statement of `lem:central-corona-corner`
(compressing by a projection commuting with the image and passing to a
coordinate subsequence) is a different assertion and is not restated here. -/
def PrintedPolarCoordinateUnitaryLifts : Prop :=
  ∀ (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)),
    letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ u : unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      ∃ v : ∀ n, Matrix.unitaryGroup (X n) ℂ,
        unitarySequenceToCorona X v = u

/-- Closed proof of the sixth printed sentence. -/
theorem manuscriptPrintedPolarCoordinateUnitaryLifts :
    PrintedPolarCoordinateUnitaryLifts := by
  intro X hX
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro u
  obtain ⟨q, hq⟩ := unitaryCoronaToCStarCoronaUnitary_surjective X u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨v, (unitaryCoronaToCStarCoronaUnitary_mk X v).symm.trans hq⟩

/-! ## Sentence 7 -/

/-- **"At stage `n`, take a direct sum of one coordinate from each of the
first `n` models.  Choose each coordinate far enough out that the first `n`
multiplication defects are at most `1/n` and the designated value at `x_j`
retains at least half of its corona-norm separation."**  A finite list of
coordinate blocks is the printed direct sum; the four clauses are its
unitarity, the positivity of its dimension, the defect estimate at the printed
tolerance `1/n`, and the retention of the separation of any designated block.

Two differences from the printed sentence.  The defect estimate holds at every
nonnegative tolerance — `1/n` is stated because that is what is printed, not
because it is the limit of the method.  And the retention clause is sharper
than "at least half": since the operator norm of a block diagonal is the
maximum of the block norms, the direct sum retains the *whole* separation of
the designated block; both that and the printed half are stated.  The constant
retained is the separation of the chosen coordinate, and no arithmetic
relation between it and a corona norm is asserted here. -/
def PrintedStageDirectSum : Prop :=
  ∀ (G : Type) [Group G] (Bs : List (UnitaryBlock G)),
    (∀ g : G, blockListMap Bs g ∈
        Matrix.unitaryGroup (blockListModel Bs) ℂ) ∧
      (∀ B ∈ Bs, 0 < Fintype.card B.model →
        0 < Fintype.card (blockListModel Bs)) ∧
      (∀ (n : ℕ) (g h : G),
        (∀ B ∈ Bs,
            ‖(B.map (g * h) : Matrix B.model B.model ℂ) -
              (B.map g : Matrix B.model B.model ℂ) *
                (B.map h : Matrix B.model B.model ℂ)‖ ≤ 1 / (n : ℝ)) →
          ‖blockListMap Bs (g * h) -
            blockListMap Bs g * blockListMap Bs h‖ ≤ 1 / (n : ℝ)) ∧
      (∀ B ∈ Bs, ∀ (delta : ℝ) (x : G),
        delta ≤ ‖(B.map x : Matrix B.model B.model ℂ) - B.map 1‖ →
          delta ≤ ‖blockListMap Bs x - blockListMap Bs 1‖ ∧
            delta / 2 ≤ ‖blockListMap Bs x - blockListMap Bs 1‖)

/-- Closed proof of the seventh printed sentence. -/
theorem manuscriptPrintedStageDirectSum : PrintedStageDirectSum := by
  intro G _ Bs
  refine ⟨fun g ↦ blockListMap_mem_unitaryGroup Bs g, ?_, ?_, ?_⟩
  · intro B hB hpos
    exact card_blockListModel_pos_of_mem hB hpos
  · intro n g h hdefect
    exact norm_blockListMap_mul_sub_le G Bs g h
      (div_nonneg zero_le_one (Nat.cast_nonneg n)) hdefect
  · intro B hB delta x hdelta
    have hle := norm_blockListMap_sub_ge_of_mem hB x 1
    have hnn : (0 : ℝ) ≤ ‖blockListMap Bs x - blockListMap Bs 1‖ :=
      norm_nonneg _
    exact ⟨by linarith, by linarith⟩

/-! ## Sentence 8 -/

/-- **"Such coordinates exist arbitrarily far out: the defects converge to
zero, while the quotient norm is a limsup."**  Two clauses, one for each
printed reason.  First: for a marked operator-norm almost representation, an
arbitrary finite set of multiplication tests, an arbitrary tolerance and an
arbitrary starting index, there is a *later* coordinate at which every test is
met and the mark is still separated — this is the "arbitrarily far out"
selection, and its proof is exactly that finitely many eventual bounds are
eventually simultaneous.  Second: the corona quotient norm of a class is the
limsup of the coordinate operator norms, which is what makes the separation
survive coordinatewise.

In the tree's marked almost representations the separation holds at *every*
coordinate, not merely at cofinally many, so the first clause asserts it at
the selected coordinate without further hypothesis. -/
def PrintedCoordinatesExistArbitrarilyFarOut : Prop :=
  (∀ (G : Type) [Group G] (z : G) (A : MarkedOpAlmostRepresentation G z)
      (S : Finset (G × G)) (eps : ℝ), 0 < eps → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧
        (∀ p ∈ S,
          ‖(A.map n (p.1 * p.2) : Matrix (A.model n) (A.model n) ℂ) -
            (A.map n p.1 : Matrix (A.model n) (A.model n) ℂ) *
              (A.map n p.2 : Matrix (A.model n) (A.model n) ℂ)‖ ≤ eps) ∧
        A.separation ≤
          ‖(A.map n z : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖) ∧
    (∀ (Y : ℕ → Type) [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)]
        [∀ n, Nonempty (Y n)] (a : BoundedMatrixSequence Y),
      ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal Y Filter.cofinite) a‖ =
        Filter.limsup (fun n ↦ ‖a n‖) Filter.cofinite)

/-- Closed proof of the eighth printed sentence. -/
theorem manuscriptPrintedCoordinatesExistArbitrarilyFarOut :
    PrintedCoordinatesExistArbitrarilyFarOut := by
  constructor
  · intro G _ z A S eps heps N
    have hall : ∀ᶠ n in Filter.atTop, ∀ p ∈ S,
        ‖(A.map n (p.1 * p.2) : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n p.1 : Matrix (A.model n) (A.model n) ℂ) *
            (A.map n p.2 : Matrix (A.model n) (A.model n) ℂ)‖ ≤ eps := by
      rw [Filter.eventually_all_finset]
      intro p _
      exact Filter.eventually_atTop.mpr
        (A.asymptoticallyMultiplicative p.1 p.2 eps heps)
    obtain ⟨n, hn, hdefect⟩ := ((Filter.eventually_ge_atTop N).and hall).exists
    exact ⟨n, hn, hdefect, A.marked_separated n⟩
  · intro Y _ _ _ a
    exact norm_filterMatrixCorona_mk_eq_limsup Y Filter.cofinite a

/-! ## Sentence 9 -/

/-- **"The resulting operator-norm asymptotic representation detects every
`x_j`, so its corona homomorphism is faithful on `G/R`.  Thus `G/R` is
MF."**  Three clauses: one genuine corona representation of `G` whose kernel is
exactly the radical (that is "detects every `x_j`"), the faithful corona
homomorphism on `G/R` it induces, and the MF property of `G/R` in the literal
Carrión–Dadarlat–Eckhardt sense. -/
def PrintedQuotientDetectedAndMF : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    (∃ (X : ℕ → FiniteModel), ∃ hX : ∀ n, 0 < Fintype.card (X n),
        letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
        ∃ pi : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
          pi.ker = actualCoronaMFResidual G) ∧
      (∃ (X : ℕ → FiniteModel), ∃ hX : ∀ n, 0 < Fintype.card (X n),
        letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
        ∃ piBar : (G ⧸ actualCoronaMFResidual G) →*
            unitary (NormMatrixCStarCorona (fun n ↦ X n)),
          Function.Injective piBar) ∧
      IsCDEOperatorMF (G ⧸ actualCoronaMFResidual G)

/-- Closed proof of the ninth printed sentence. -/
theorem manuscriptPrintedQuotientDetectedAndMF :
    PrintedQuotientDetectedAndMF := by
  intro G _ _
  refine ⟨exists_actualCoronaRepresentation_ker_eq_actualCoronaMFResidual,
    ?_, actualCoronaMFQuotient_isCDEOperatorMF⟩
  obtain ⟨d, hd, _hmono, rho, hrho⟩ :=
    actualCoronaMFQuotient_isCDEOperatorMF (G := G)
  exact ⟨fun n ↦ naturalFiniteModel (d n), by simpa using hd, rho, hrho⟩

/-! ## Sentence 10 -/

/-- **"Applied to `G/N`, the same argument says that `G/N` is MF exactly when
the intersection of the kernels of all MF-target maps killing `N` is `N`,
which is the asserted closure criterion."**  The first clause identifies the
MF closure of `N` with that intersection of kernels; the second is the printed
criterion itself. -/
def PrintedClosureCriterion : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (N : Subgroup G) [N.Normal],
    (∀ x : G, x ∈ actualCoronaMFClosure N ↔
        ∀ (X : ℕ → FiniteModel), ∀ hX : ∀ n, 0 < Fintype.card (X n),
          letI : ∀ n, Nonempty (X n) :=
            fun n ↦ Fintype.card_pos_iff.mp (hX n)
          ∀ rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
            (∀ y ∈ N, rho y = 1) → rho x = 1) ∧
      (IsCDEOperatorMF (G ⧸ N) ↔ actualCoronaMFClosure N = N)

/-- Closed proof of the tenth printed sentence. -/
theorem manuscriptPrintedClosureCriterion : PrintedClosureCriterion := by
  intro G _ _ N _
  exact ⟨fun _ ↦ mem_actualCoronaMFClosure_iff,
    (actualCoronaMFClosure_eq_self_iff N).symm⟩

/-! ## The printed proof, assembled -/

/-- Every sentence of the printed proof of `prop:mf-residual-calculus`, in
printed order, as one closed proposition. -/
def PrintedResidualCalculusProof : Prop :=
  PrintedIntersectionOfKernelsIsNormal ∧
    PrintedFullInvarianceThroughComposition ∧
    PrintedEnumerationsOfTheQuotient ∧
    PrintedCoronaDetectorAtEachMarkedClass ∧
    PrintedDetectorKillsRadicalAndDescends ∧
    PrintedPolarCoordinateUnitaryLifts ∧
    PrintedStageDirectSum ∧
    PrintedCoordinatesExistArbitrarilyFarOut ∧
    PrintedQuotientDetectedAndMF ∧
    PrintedClosureCriterion

/-- Closed proof of the complete printed proof of
`prop:mf-residual-calculus`. -/
theorem manuscriptPrintedResidualCalculusProof :
    PrintedResidualCalculusProof :=
  ⟨manuscriptPrintedIntersectionOfKernelsIsNormal,
    manuscriptPrintedFullInvarianceThroughComposition,
    manuscriptPrintedEnumerationsOfTheQuotient,
    manuscriptPrintedCoronaDetectorAtEachMarkedClass,
    manuscriptPrintedDetectorKillsRadicalAndDescends,
    manuscriptPrintedPolarCoordinateUnitaryLifts,
    manuscriptPrintedStageDirectSum,
    manuscriptPrintedCoordinatesExistArbitrarilyFarOut,
    manuscriptPrintedQuotientDetectedAndMF,
    manuscriptPrintedClosureCriterion⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
