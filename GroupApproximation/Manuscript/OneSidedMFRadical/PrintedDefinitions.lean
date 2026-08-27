import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.MFDefinitions
import GroupApproximation.Sofic.WeakMFUltraproduct

/-!
# The Introduction's definitions, as checked statements

`non_mf_groups_exist.tex`, `\section{Introduction}`, from the first paragraph
through the definition of the MF radical.  Everything asserted there before the
first numbered result is stated here as a closed `Prop` over the development's
own objects.

The Introduction makes four assertions of this kind.

1. **The corona and its denominator.**  `Q_d = ∏_n M_{d_n}(ℂ) / ⊕_n M_{d_n}(ℂ)`
   with `⊕_n M_{d_n}(ℂ) = {(x_n) : ‖x_n‖ → 0}` the `c₀`-direct sum.  The
   development's numerator is `BoundedMatrixSequence`, mathlib's dependent
   `ℓ∞`, and its denominator is `nullMatrixSequenceIdeal` at the cofinite
   filter.  `mem_nullMatrixSequenceIdeal_cofinite_iff` says that the ideal is
   *literally* the printed set: membership is exactly `‖x_n‖ → 0` as `n → ∞`
   (`Nat.cofinite_eq_atTop` converts the filter).
   `normMatrixCStarCoronaMk_eq_zero_iff_tendsto` says the quotient map kills
   exactly those sequences, and `normMatrixCStarCoronaMk_surjective` (in
   `Analysis.NormMatrixCorona`) says every corona element is the class of a
   bounded matrix sequence.  The printed norm formula `‖[A_n]‖ = lim ‖A_n‖` is
   already `UltraproductAdjointAmbient.kt_04_norm_eq_limsup`, proved from
   `norm_filterMatrixCorona_mk_eq_limsup`, and is not restated here.

2. **"Equivalently, an MF group admits finite-dimensional unitary models whose
   multiplicative defects tend to zero in operator norm and which
   asymptotically separate its nonidentity elements."**  The development's
   object for such a family is `WeakMFApproximation`, whose fields are exactly
   the two printed clauses.  `PrintedMFUnitaryModels` states the equivalence in
   *both* directions and with the data unbundled, so that the printed sentence
   can be read off the statement without unfolding a structure.

   One caveat, stated here rather than hidden: the equivalence is proved with
   the separation clause in its *all-pairs* form (`g ≠ h` are eventually
   `delta`-separated), which is the form `WeakMFApproximation` carries and the
   form the ultraproduct embedding consumes.  The literally printed clause
   separates *nonidentity elements from the identity*; that weaker-looking form
   is delivered here only in the forward direction, by
   `isCDEOperatorMF_exists_separating_unitary_models`.  The converse from the
   nonidentity form alone is not in the development and is not claimed.

3. **"The image of a corona homomorphism from `G` is countable and is itself
   MF; conversely, every MF target embeds in a norm matrix corona."**  Both
   halves are `PrintedCoronaImagesAndTargets`.  The first half is
   `CoronaImageNormalKazhdan.nk_02_countable_mf_image` read in the genuine
   C-star corona rather than in the unitary-sequence corona;
   `coronaImage_countable` and `coronaImage_isOperatorMF` are that reading.
   The second half is the definition of `IsCDEOperatorMF` with its
   strictly-increasing-dimension clause dropped
   (`isCDEOperatorMF_exists_coronaEmbedding`), together with its converse
   (`isCDEOperatorMF_of_coronaEmbedding`): a countable group is MF exactly when
   it embeds in the unitary group of some norm matrix corona.

4. **`Rad_MF(G) = cl_MF^G(1)`, and `G` is MF precisely when `Rad_MF(G)` is
   trivial.**  Already carried, and deliberately *not* restated here:
   `LiteralMFClosure.literalMFClosure_bot` and its closed wrapper
   `manuscriptMFRadicalIsLiteralClosureOfTrivial` are the first identity, and
   the fourth clause of `LiteralMFClosure.LiteralMFResidualCalculus` --
   `isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot` -- is the second.
   Likewise the following sentence, "if `Rad_MF(G) = G`, every homomorphism
   from `G` to an MF group is trivial", is
   `PrintedCriterion.manuscriptFullRadicalKillsMFTargets`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

/-! ## 1.  The denominator is the `c₀`-direct sum

`⊕_n M_{d_n}(ℂ) = {(x_n) ∈ ∏_n M_{d_n}(ℂ) : ‖x_n‖ → 0}`. -/

/-- The development's null ideal at a filter `l` is, by definition, the set of
bounded matrix sequences whose coordinate operator norms tend to zero along
`l`. -/
theorem mem_nullMatrixSequenceIdeal_iff (X : ℕ → Type u) [∀ n, Fintype (X n)]
    [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)] (l : Filter ℕ)
    (a : BoundedMatrixSequence X) :
    a ∈ nullMatrixSequenceIdeal X l ↔ Tendsto (fun n ↦ ‖a n‖) l (nhds 0) :=
  Iff.rfl

/-- **The printed denominator.**  The ideal divided out in the norm matrix
corona is literally the `c₀`-direct sum: a bounded matrix sequence lies in it
exactly when `‖x_n‖ → 0` as `n → ∞`. -/
theorem mem_nullMatrixSequenceIdeal_cofinite_iff (X : ℕ → Type u)
    [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]
    (a : BoundedMatrixSequence X) :
    a ∈ nullMatrixSequenceIdeal X cofinite ↔
      Tendsto (fun n ↦ ‖a n‖) atTop (nhds 0) := by
  rw [mem_nullMatrixSequenceIdeal_iff X cofinite a, Nat.cofinite_eq_atTop]

/-- **The printed quotient.**  A bounded matrix sequence dies in the norm
matrix corona exactly when its coordinate operator norms tend to zero. -/
theorem normMatrixCStarCoronaMk_eq_zero_iff_tendsto (X : ℕ → Type u)
    [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]
    (a : BoundedMatrixSequence X) :
    normMatrixCStarCoronaMk X a = 0 ↔
      Tendsto (fun n ↦ ‖a n‖) atTop (nhds 0) := by
  rw [normMatrixCStarCoronaMk_eq_zero_iff X a]
  exact mem_nullMatrixSequenceIdeal_cofinite_iff X a

/-- Closed form of the Introduction's two displays: the norm matrix corona is
the quotient of the uniformly bounded matrix sequences -- every corona element
is the class of one -- by the `c₀`-direct sum, and the `c₀`-direct sum is
exactly the set of sequences whose operator norms tend to zero.

The coordinates are arbitrary nonempty finite models rather than `Fin (d n)`;
the printed `d_n` is `Fintype.card (X n)`, and the natural-dimension instance
is `X n = naturalFiniteModel (d n)`. -/
def PrintedCoronaDenominator : Prop :=
  ∀ (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)],
    Function.Surjective (normMatrixCStarCoronaMk (fun n ↦ X n)) ∧
      ∀ a : BoundedMatrixSequence (fun n ↦ X n),
        (a ∈ nullMatrixSequenceIdeal (fun n ↦ X n) cofinite ↔
            Tendsto (fun n ↦ ‖a n‖) atTop (nhds 0)) ∧
          (normMatrixCStarCoronaMk (fun n ↦ X n) a = 0 ↔
            Tendsto (fun n ↦ ‖a n‖) atTop (nhds 0))

/-- Closed proof of the Introduction's description of the norm matrix
corona. -/
theorem manuscriptCoronaDenominator : PrintedCoronaDenominator := by
  intro X _inst
  exact ⟨normMatrixCStarCoronaMk_surjective (fun n ↦ X n), fun a ↦
    ⟨mem_nullMatrixSequenceIdeal_cofinite_iff (fun n ↦ X n) a,
      normMatrixCStarCoronaMk_eq_zero_iff_tendsto (fun n ↦ X n) a⟩⟩

/-! ## 2.  MF means asymptotically multiplicative, asymptotically separating
unitary models

"Equivalently, an MF group admits finite-dimensional unitary models whose
multiplicative defects tend to zero in operator norm and which asymptotically
separate its nonidentity elements." -/

/-- **The printed equivalence, bundled.**  A countable group is MF exactly when
it admits a sequential family of finite-dimensional unitary models with
operator-norm multiplicative defect tending to zero and a fixed positive
asymptotic separation.  `WeakMFApproximation` is precisely that family. -/
theorem isCDEOperatorMF_iff_nonempty_weakMFApproximation (G : Type u) [Group G]
    [Countable G] :
    IsCDEOperatorMF G ↔ Nonempty (WeakMFApproximation G) := by
  constructor
  · intro h
    have hone : IsNormApproximable G 1 :=
      OperatorMFLocalNormalization.isNormApproximable_one
        ((isCDEOperatorMF_iff_isOperatorMF G).mp h)
    exact exists_weakMFApproximation (by norm_num : (0 : ℝ) < 1) hone
  · rintro ⟨A⟩
    let U : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
    have hU : ((U : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
      Ultrafilter.of_le _
    obtain ⟨rho, hrho⟩ := A.exists_normUltraproductEmbedding hU
    have hultra : IsUltraproductMF G :=
      ⟨U, hU, A.model, A.modelNonempty, rho, hrho⟩
    exact (isCDEOperatorMF_iff_isOperatorMF G).mpr
      (isGroupTheoreticMF_iff_isOperatorMF.mp hultra.isGroupTheoreticMF)

/-- Closed form of the Introduction's "equivalently" sentence, with the models
unbundled.  A countable group is MF exactly when there are finite-dimensional
unitary models `V_{g,n}` on positive-dimensional coordinates whose
multiplicative defects tend to zero in operator norm, together with one fixed
`delta > 0` at which distinct group elements are eventually separated.

The separation clause is the all-pairs form; the printed nonidentity form is
its specialization at `h = 1`, recorded by
`isCDEOperatorMF_exists_separating_unitary_models`. -/
def PrintedMFUnitaryModels : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    IsCDEOperatorMF G ↔
      ∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ)
        (delta : ℝ), (∀ n, 0 < Fintype.card (X n)) ∧ 0 < delta ∧
          (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
            ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
              (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
          (∀ g h : G, g ≠ h → ∃ N, ∀ n ≥ N,
            delta ≤ ‖(V n g : Matrix (X n) (X n) ℂ) - V n h‖)

/-- Closed proof of the Introduction's "equivalently" sentence. -/
theorem manuscriptMFUnitaryModels : PrintedMFUnitaryModels := by
  intro G _ _
  constructor
  · intro h
    obtain ⟨A⟩ := (isCDEOperatorMF_iff_nonempty_weakMFApproximation G).mp h
    exact ⟨A.model, A.map, A.separation, A.modelNonempty, A.separation_pos,
      A.asymptoticallyMultiplicative, A.separatedEventually⟩
  · rintro ⟨X, V, delta, hX, hdelta, hmul, hsep⟩
    refine (isCDEOperatorMF_iff_nonempty_weakMFApproximation G).mpr ⟨?_⟩
    exact
      { separation := delta
        separation_pos := hdelta
        model := X
        modelNonempty := hX
        map := V
        asymptoticallyMultiplicative := hmul
        separatedEventually := hsep }

/-- **The printed sentence verbatim, forward direction.**  An MF group admits
finite-dimensional unitary models whose multiplicative defects tend to zero in
operator norm and which asymptotically separate its nonidentity elements from
the identity.

Only this direction is stated in the nonidentity form.  The converse is
available in the development through the all-pairs separation clause of
`PrintedMFUnitaryModels`; deducing MF-ness from nonidentity separation alone is
not proved here. -/
theorem isCDEOperatorMF_exists_separating_unitary_models (G : Type) [Group G]
    [Countable G] (h : IsCDEOperatorMF G) :
    ∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ)
      (delta : ℝ), (∀ n, 0 < Fintype.card (X n)) ∧ 0 < delta ∧
        (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
          ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
            (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
        (∀ g : G, g ≠ 1 → ∃ N, ∀ n ≥ N,
          delta ≤ ‖(V n g : Matrix (X n) (X n) ℂ) - V n 1‖) := by
  obtain ⟨X, V, delta, hX, hdelta, hmul, hsep⟩ :=
    (manuscriptMFUnitaryModels G).mp h
  exact ⟨X, V, delta, hX, hdelta, hmul, fun g hg ↦ hsep g 1 hg⟩

/-! ## 3.  Corona images and MF targets

"The image of a corona homomorphism from `G` is countable and is itself MF;
conversely, every MF target embeds in a norm matrix corona." -/

/-- **The image of a corona homomorphism is countable.**  Countability is
inherited from the source, because the range restriction is surjective. -/
theorem coronaImage_countable (G : Type u) [Group G] [Countable G]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (Theta : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
    Countable Theta.range :=
  Function.Surjective.countable Theta.rangeRestrict_surjective

/-- **The image of a corona homomorphism is itself MF.**  The image sits inside
the very corona that received the representation, so its inclusion, read
through the polar-correction isomorphism `normMatrixCoronaUnitaryEquiv`, is a
faithful representation on the same coordinate sequence.  This is
`CoronaImageNormalKazhdan.nk_02_countable_mf_image` for a homomorphism into the
genuine C-star corona. -/
theorem coronaImage_isOperatorMF (G : Type u) [Group G]
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    [∀ n, Nonempty (X n)]
    (Theta : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
    IsOperatorMF Theta.range :=
  ⟨X, hX,
    (normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp Theta.range.subtype,
    (normMatrixCoronaUnitaryEquiv X).symm.injective.comp Subtype.val_injective⟩

/-- **Every countable group embedded in a norm matrix corona is MF.**  This is
the converse half of the printed "conversely" clause, and it is what upgrades
`coronaImage_isOperatorMF` to the printed predicate on the image. -/
theorem isCDEOperatorMF_of_coronaEmbedding (M : Type u) [Group M] [Countable M]
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    [∀ n, Nonempty (X n)]
    (iota : M →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (hiota : Function.Injective iota) : IsCDEOperatorMF M :=
  (isCDEOperatorMF_iff_isOperatorMF M).mpr
    ⟨X, hX, (normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp iota,
      (normMatrixCoronaUnitaryEquiv X).symm.injective.comp hiota⟩

/-- **Every MF target embeds in a norm matrix corona.**  This is the definition
of `IsCDEOperatorMF` made explicit: the strictly-increasing-dimension clause
carried by that definition is extra, and is dropped here, leaving exactly the
printed statement. -/
theorem isCDEOperatorMF_exists_coronaEmbedding (M : Type u) [Group M]
    [Countable M] (hM : IsCDEOperatorMF M) :
    ∃ d : ℕ → ℕ, ∃ hd : ∀ n, 0 < d n,
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      ∃ iota : M →* unitary (NormMatrixCStarCorona
        (fun n ↦ naturalFiniteModel (d n))), Function.Injective iota := by
  obtain ⟨d, hd, -, rho, hrho⟩ := hM
  exact ⟨d, hd, rho, hrho⟩

/-- Closed form of the Introduction's sentence on corona images and MF targets.

The first clause is the printed "the image of a corona homomorphism from `G` is
countable and is itself MF", with MF-ness in the unitary-sequence-corona form
`IsOperatorMF`; the second clause converts that form into the printed predicate
`IsCDEOperatorMF` once countability -- the first clause -- is in hand, since the
image is a countable group embedded in a norm matrix corona by its own
inclusion.  The third clause is the printed converse. -/
def PrintedCoronaImagesAndTargets : Prop :=
  (∀ (G : Type) [Group G] [Countable G] (X : ℕ → FiniteModel)
      [∀ n, Nonempty (X n)], (∀ n, 0 < Fintype.card (X n)) →
      ∀ Theta : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
        Countable Theta.range ∧ IsOperatorMF Theta.range) ∧
    (∀ (M : Type) [Group M] [Countable M] (X : ℕ → FiniteModel)
      [∀ n, Nonempty (X n)], (∀ n, 0 < Fintype.card (X n)) →
      ∀ iota : M →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
        Function.Injective iota → IsCDEOperatorMF M) ∧
    (∀ (M : Type) [Group M] [Countable M], IsCDEOperatorMF M →
      ∃ d : ℕ → ℕ, ∃ hd : ∀ n, 0 < d n,
        letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
          fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
        ∃ iota : M →* unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))), Function.Injective iota)

/-- Closed proof of the Introduction's sentence on corona images and MF
targets. -/
theorem manuscriptCoronaImagesAndTargets : PrintedCoronaImagesAndTargets := by
  refine ⟨?_, ?_, ?_⟩
  · intro G _ _ X _inst hX Theta
    exact ⟨coronaImage_countable G X Theta, coronaImage_isOperatorMF G X hX Theta⟩
  · intro M _ _ X _inst hX iota hiota
    exact isCDEOperatorMF_of_coronaEmbedding M X hX iota hiota
  · intro M _ _ hM
    exact isCDEOperatorMF_exists_coronaEmbedding M hM

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
