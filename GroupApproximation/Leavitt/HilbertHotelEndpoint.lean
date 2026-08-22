import GroupApproximation.Leavitt.HilbertHotelCoverBlock

/-!
# The Hilbert-hotel endpoints

The Hilbert-hotel construction produces **two** groups, and they are different
groups with different virtues.  Nothing below identifies them; the point of
this module is to say what each one is for.

* `Cover.Model` is `EL₁₆(L_{𝔽₂}(1,2))`, an explicit group of `16 × 16` matrices
  over the binary Leavitt algebra.  It is finitely *generated* but is not given
  by a presentation, and it carries the compression core directly
  (`HilbertHotelModelNonMF`).  Its virtue is concreteness: it is the rank-`16`
  member of the Theorem A family, so it is also **not sofic**, and the two
  negative properties hold of one and the same group.

* `CoverBlock.HotelGroup` is the two-block Shalom cover
  (`HilbertHotelCoverBlock`).  It is finitely **presented**, which the model is
  not, at the cost of being a presentation rather than a matrix group.

The two are related by `CoverBlock.blockToModel`, a homomorphism from the cover
to the model, and *only* by that: nothing in this development identifies the two
groups, and nothing claims that map is injective.  So neither headline implies
the other, and each keeps a property the other does not have -- concreteness on
one side, a finite presentation on the other.

## What the MF statements say

`CoronaMFInvisible x` says every homomorphism of the group into the unitary
group of a standard cofinite norm-matrix corona kills `x`; `cdeMFResidual = ⊤`
is the same sentence for the literal Carrión--Dadarlat--Eckhardt coronas, and
says the group is equal to its own MF radical.  Both are strictly stronger
than `¬ IsOperatorMF`, which says only that no corona representation is
*injective*: the full-radical statement says every corona representation is
trivial.  A group equal to its own MF radical is as far from MF as a group can
be -- it has no nontrivial corona representation at all.

## Nothing is proved here that is not a repackaging

Every conjunct below is a theorem of `HilbertHotelModelNonMF`,
`HilbertHotelCoverBlock`, `Steinberg.BinaryLeavitt` or `ElementaryGroup`.  The
short proofs in this file convert a residual identity into its elementwise
form, or a corona statement into its literal CDE form, and nothing else.
-/

namespace GroupApproximation
namespace HilbertHotel
namespace Endpoint

/-! ## The model `EL₁₆(L_{𝔽₂}(1,2))` -/

/-- **Every element of the model is corona-invisible.**  The elementwise form
of `Cover.coronaMFResidual_model_eq_top`, read straight off the normal-Kazhdan
criterion at `K = ⊤`. -/
theorem model_coronaMFInvisible (x : Cover.Model) : CoronaMFInvisible x :=
  QuestionTwoReduction.coronaMFInvisible_of_mem_normal_kazhdan_defect
    Cover.modelCore ⊤ Cover.top_hasKazhdanPropertyT_model
    Cover.top_le_defectNormal (Subgroup.mem_top x)

/-- **The model endpoint.**  An explicit countable Kazhdan group which is equal
to its own MF radical, and therefore not operator MF in either the corona or
the literal CDE formulation.  Unconditional. -/
theorem model_profile :
    Countable Cover.Model ∧
      Nontrivial Cover.Model ∧
      HasKazhdanPropertyT.{0, 0} Cover.Model ∧
      (∀ x : Cover.Model, CoronaMFInvisible x) ∧
      cdeMFResidual Cover.Model = ⊤ ∧
      ¬ IsOperatorMF Cover.Model ∧
      ¬ IsCDEOperatorMF Cover.Model :=
  ⟨inferInstance, Cover.model_nontrivial, Cover.model_hasKazhdanPropertyT,
    model_coronaMFInvisible, Cover.cdeMFResidual_model_eq_top,
    Cover.not_isOperatorMF_model, Cover.not_isCDEOperatorMF_model⟩

/-! ### The model is the rank-sixteen member of the Theorem A family

`Cover.Model` is `BinaryLeavittSteinberg.ElementaryBase 16` on the nose, which
is the rank-`16` member of the family Theorem A is about.  So Theorem A's
clauses are clauses about *this* group, and in particular the Hilbert-hotel
model is **not sofic**.  That is what makes the pair of negative properties
worth stating together: they hold of a single explicit group, rather than of
two groups built for two different purposes.

Each clause is taken at the `ElementaryBase 16` spelling rather than through
`universalLeavitt_profile`, whose index reads `15 + 1`; the statements are the
same but the spelling here needs no arithmetic to line up. -/

theorem model_fg : Group.FG Cover.Model :=
  elementaryGroup_finitelyGenerated 16 (by omega)

theorem model_infinite : Infinite Cover.Model :=
  elementaryGroup_infinite (R := UniversalLeavitt.BinaryLeavittAlgebra)
    (0 : Fin 16) 1 (by decide)

/-- **The Hilbert-hotel model is not sofic.**  Theorem A at rank `16`. -/
theorem model_not_isSofic : ¬ IsSofic Cover.Model :=
  BinaryLeavittSteinberg.elementaryBase_not_isSofic (by omega)

/-- **The sharp model statement.**  One explicit finitely generated infinite
Kazhdan matrix group which is simultaneously not sofic and equal to its own MF
radical. -/
theorem model_full_profile :
    Countable Cover.Model ∧
      Group.FG Cover.Model ∧
      Infinite Cover.Model ∧
      Nontrivial Cover.Model ∧
      HasKazhdanPropertyT.{0, 0} Cover.Model ∧
      ¬ IsSofic Cover.Model ∧
      (∀ x : Cover.Model, CoronaMFInvisible x) ∧
      cdeMFResidual Cover.Model = ⊤ ∧
      ¬ IsOperatorMF Cover.Model ∧
      ¬ IsCDEOperatorMF Cover.Model :=
  ⟨inferInstance, model_fg, model_infinite, Cover.model_nontrivial,
    Cover.model_hasKazhdanPropertyT, model_not_isSofic, model_coronaMFInvisible,
    Cover.cdeMFResidual_model_eq_top, Cover.not_isOperatorMF_model,
    Cover.not_isCDEOperatorMF_model⟩

/-! ## The finitely presented cover -/

/-- **Full MF radical, corona form.**  `CoverBlock.coverGroup₂_full_mf_radical`
read as an identity of subgroups. -/
theorem hotelGroup_coronaMFResidual_eq_top :
    coronaMFResidual CoverBlock.HotelGroup = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  exact CoverBlock.coverGroup₂_full_mf_radical CoverBlock.blockCoverInputs
    CoverBlock.coverBlockResiduals x

/-- **Full MF radical, literal CDE form.** -/
theorem hotelGroup_cdeMFResidual_eq_top :
    cdeMFResidual CoverBlock.HotelGroup = ⊤ := by
  rw [cdeMFResidual_eq_coronaMFResidual]
  exact hotelGroup_coronaMFResidual_eq_top

/-- The literal CDE form of the negative conclusion for the cover. -/
theorem hotelGroup_not_isCDEOperatorMF :
    ¬ IsCDEOperatorMF CoverBlock.HotelGroup := by
  haveI : Nontrivial CoverBlock.HotelGroup :=
    CoverBlock.coverGroup₂_nontrivial CoverBlock.blockCoverInputs
      CoverBlock.coverBlockResiduals
  rw [isCDEOperatorMF_iff_cdeMFResidual_eq_bot, hotelGroup_cdeMFResidual_eq_top]
  exact top_ne_bot

/-- **The defect saturates the cover.**  The whole finitely presented group is
the normal closure of the single identified defect element.  That is what puts
the normal-Kazhdan criterion at `K = ⊤` rather than at a proper subgroup, so it
is the reason the criterion applies at all; `CoverBlock.hotelGroup_endpoint`
drops the clause only because it names an internal element. -/
theorem hotelGroup_defect_normallyGenerates :
    Subgroup.normalClosure
        ({CoverBlock.blockDefect CoverBlock.blockCoverInputs
            CoverBlock.coverBlockResiduals} : Set CoverBlock.HotelGroup) = ⊤ :=
  CoverBlock.defectClosure_eq_top CoverBlock.blockCoverInputs
    CoverBlock.coverBlockResiduals

/-- **The finitely presented endpoint.**  `CoverBlock.hotelGroup_endpoint` with
the two literal CDE clauses appended. -/
theorem hotelGroup_profile :
    Group.IsFinitelyPresented CoverBlock.HotelGroup ∧
      Countable CoverBlock.HotelGroup ∧
      Nontrivial CoverBlock.HotelGroup ∧
      HasKazhdanPropertyT.{0, 0} CoverBlock.HotelGroup ∧
      (∀ x : CoverBlock.HotelGroup, CoronaMFInvisible x) ∧
      cdeMFResidual CoverBlock.HotelGroup = ⊤ ∧
      ¬ IsOperatorMF CoverBlock.HotelGroup ∧
      ¬ IsCDEOperatorMF CoverBlock.HotelGroup := by
  obtain ⟨hfp, hcount, hne, hT, hmf, hnot⟩ := CoverBlock.hotelGroup_endpoint
  exact ⟨hfp, hcount, hne, hT, hmf, hotelGroup_cdeMFResidual_eq_top, hnot,
    hotelGroup_not_isCDEOperatorMF⟩

/-! ## The two existence statements

Both are named propositions with an empty outer telescope, so that the
advertised endpoint accepts nothing from its caller. -/

/-- Existence of an explicit finitely generated infinite Kazhdan group which is
not sofic and is equal to its own MF radical. -/
def NonsoficFullMFRadicalGroupExists : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Countable G),
    Group.FG G ∧ Infinite G ∧ HasKazhdanPropertyT.{0, 0} G ∧
      ¬ IsSofic G ∧ cdeMFResidual G = ⊤ ∧ ¬ IsOperatorMF G

/-- Existence of a finitely presented Kazhdan group equal to its own MF
radical. -/
def FinitelyPresentedFullMFRadicalGroupExists : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Countable G),
    Group.IsFinitelyPresented G ∧ Nontrivial G ∧
      HasKazhdanPropertyT.{0, 0} G ∧
      cdeMFResidual G = ⊤ ∧ ¬ IsOperatorMF G ∧ ¬ IsCDEOperatorMF G

/-- **A single group carries both negative properties.**  The Hilbert-hotel
model is not sofic and is equal to its own MF radical. -/
theorem nonsofic_full_mf_radical_groups_exist :
    NonsoficFullMFRadicalGroupExists :=
  ⟨Cover.Model, inferInstance, inferInstance, model_fg, model_infinite,
    Cover.model_hasKazhdanPropertyT, model_not_isSofic,
    Cover.cdeMFResidual_model_eq_top, Cover.not_isOperatorMF_model⟩

/-- **The finitely presented headline.**  There is a finitely presented Kazhdan
group equal to its own MF radical. -/
theorem finitelyPresented_full_mf_radical_groups_exist :
    FinitelyPresentedFullMFRadicalGroupExists := by
  obtain ⟨hfp, -, hne, hT, -, hcde, hnot, hncde⟩ := hotelGroup_profile
  exact ⟨CoverBlock.HotelGroup, inferInstance, inferInstance, hfp, hne, hT,
    hcde, hnot, hncde⟩

end Endpoint
end HilbertHotel
end GroupApproximation
