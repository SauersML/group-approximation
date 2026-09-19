import GroupApproximation.Leavitt.HilbertHotelBinary
import GroupApproximation.Leavitt.HilbertHotelDefectNormal
import GroupApproximation.Leavitt.UniversalRankFour
import GroupApproximation.Steinberg.BinaryLeavitt
import GroupApproximation.Kazhdan.ShalomFinitePresentation
import GroupApproximation.Kazhdan.KazhdanUniverseDescent
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Sofic.KazhdanCompressionCore
import GroupApproximation.Sofic.QuestionTwoReduction

/-!
# The Hilbert-hotel cover presentation

The block layer (`HilbertHotelBlocks`, `HilbertHotelSaturation`,
`HilbertHotelWhitehead`, `HilbertHotelBinary`, `HilbertHotelDefectNormal`)
supplies, inside the elementary group `E₁₆(R)` over `R = L_{𝔽₂}(1,2)`:

* a stable letter `τ = Tunit L`, elliptic (`Tunit_mem_elementaryGroup`), whose
  conjugation compresses the rank-four corner copy of `E₄(R)` by
  `a ↦ s₀ a t₀` (`Tunit_conj_corner` with `cornerUnits_elementaryUnit`);
* a mark `c = e₄₅(1)` centralizing that corner (`cornerUnits_commute_mark`) --
  the reason is index-disjointness of the two *root positions*, both corner
  indices being `< 4` against `(4,5)`, not block-disjointness as such: two
  roots in different blocks can still chain if one's column meets the other's
  row, and the proof cashes exactly `corner j ≠ 4` and `5 ≠ corner i`;
* a defect `d = e₀₂(q)` with `q = p₁ = s₁t₁` full and nonzero
  (`defect_from_conjugated_mark`, `defect_ne_one`, `q_ne_zero`), which
  normally generates the model (`normalClosure_defect_eq_top`).

This file builds the *cover presentation* above that layer: a finitely
presented Kazhdan group `CoverGroup` whose compression defect is all of it,
ready for the normal-Kazhdan criterion at `K = ⊤`.

## The architecture, and why the saturation relators are needed here

Two routes reach "the defect normally generates".

*The Steinberg route.*  If the cover is literally `St_n(R)`, then
`BinaryLeavittSteinberg.normalClosure_root_eq_top` (any rank `≥ 5`, any root,
any nonzero coefficient) says the root `x₀₂(q)` already normally generates, and
that survives every quotient identifying it with the defect.  This is what
`research/full-leavitt-idempotent-defect-saturation.md` means by "no separate
saturation family is needed".  Its cost is finite presentability of `St_n(R)`,
which is Krstic--McCool -- external.

*The Shalom route*, taken here.  The cover is
`Shalom.exists_presented_kazhdan_cover` applied to `E₁₆(R)`, so finite
presentability is `inferInstance` on a `PresentedGroup` over a `Finset` and
property `(T)` is `elementaryBase_hasKazhdanPropertyT`; both are in-repo and no
literature input is consumed.  The price is that `normalClosure_root_eq_top` is
a statement about the *model* and does **not** transfer backwards along
`CoverGroup ↠ Model`: a normal closure only pushes forward, so a surjection
gives `⟨⟨d⟩⟩ · ker = ⊤`, never `⟨⟨d⟩⟩ = ⊤`.  On this route the saturation
relators must therefore be **imposed**, one per generator, and the block
identities become the *consistency* input -- they certify that the imposed
relators are true in the model -- rather than the source of the saturation.

What the model's saturation does buy is the **words**: it says every model
element is *some* product of conjugates of the defect, and choosing such a
product (non-constructively, exactly as `liftWord` chooses a preimage) supplies
the `V_x(d)` that the imposed relator names.  So no explicit word family is
needed, and `⟨⟨d⟩⟩ = ⊤` holds in `CoverGroup` by construction.

## Open leaves

Per the save doctrine, this module carries no unproved placeholder: the
residual facts are fields of `CoverInputs` and `CoverResiduals`, taken as
arguments where they are used.  Discharging a field turns the corresponding
theorem unconditional without touching its statement.
-/

namespace GroupApproximation
namespace HilbertHotel
namespace Cover

open scoped commutatorElement

/-! ## The model group -/

/-- The model: the elementary group of the `16` frame over the binary Leavitt
algebra.  Everything the block layer proves lives here. -/
noncomputable abbrev Model : Type := ↥(BinaryLeavittSteinberg.ElementaryBase 16)

/-- The model has property `(T)`; rank `16 ≥ 2`. -/
theorem model_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} Model :=
  BinaryLeavittSteinberg.elementaryBase_hasKazhdanPropertyT (by omega)

/-! ## The Shalom cover -/

/-- A finitely presented Kazhdan cover of the model, packaged as data so that
the choice is made once. -/
structure CoverData where
  /-- The number of generators of the cover. -/
  n : ℕ
  /-- The finite relator set. -/
  rels : Finset (FreeGroup (Fin n))
  /-- The covering map onto the model. -/
  quotient :
    PresentedGroup ((rels : Finset (FreeGroup (Fin n))) :
      Set (FreeGroup (Fin n))) →* Model
  /-- The covering map is onto. -/
  quotient_surjective : Function.Surjective quotient
  /-- The cover is Kazhdan. -/
  kazhdan : HasKazhdanPropertyT.{0, 1}
    (PresentedGroup ((rels : Finset (FreeGroup (Fin n))) :
      Set (FreeGroup (Fin n))))

/-- Shalom's presentation theorem supplies a cover. -/
theorem coverData_nonempty : Nonempty CoverData := by
  obtain ⟨S, -, -, hS⟩ :=
    KazhdanFiniteGeneration.exists_symmetric_generating_finset Model
      model_hasKazhdanPropertyT
  obtain ⟨n, rels, φ, hsurj, hT⟩ :=
    Shalom.exists_presented_kazhdan_cover S hS model_hasKazhdanPropertyT
  exact ⟨⟨n, rels, φ, hsurj, hT⟩⟩

/-- The chosen cover. -/
noncomputable def coverData : CoverData := Classical.choice coverData_nonempty

/-- The generator count of the chosen cover. -/
noncomputable abbrev generatorCount : ℕ := coverData.n

/-- The relators of the chosen cover. -/
noncomputable abbrev coverRelators : Finset (FreeGroup (Fin generatorCount)) :=
  coverData.rels

/-- The cover `Δ`. -/
noncomputable abbrev Delta : Type :=
  PresentedGroup ((coverRelators : Finset (FreeGroup (Fin generatorCount))) :
    Set (FreeGroup (Fin generatorCount)))

/-- The covering map `Δ ↠ Model`. -/
noncomputable abbrev deltaQuotient : Delta →* Model := coverData.quotient

theorem deltaQuotient_surjective : Function.Surjective deltaQuotient :=
  coverData.quotient_surjective

theorem delta_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} Delta :=
  HasKazhdanPropertyT.of_max.{0, 1, 0} coverData.kazhdan

instance delta_finitelyPresented : Group.IsFinitelyPresented Delta := inferInstance

/-! ## Lifting model elements to words -/

/-- The composite from free words to the model. -/
noncomputable def freeToModel : FreeGroup (Fin generatorCount) →* Model :=
  deltaQuotient.comp (PresentedGroup.mk _)

theorem freeToModel_surjective : Function.Surjective freeToModel :=
  deltaQuotient_surjective.comp (PresentedGroup.mk_surjective _)

/-- A chosen word representing a model element. -/
noncomputable def liftWord (g : Model) : FreeGroup (Fin generatorCount) :=
  Function.surjInv freeToModel_surjective g

@[simp] theorem freeToModel_liftWord (g : Model) : freeToModel (liftWord g) = g :=
  Function.surjInv_eq freeToModel_surjective g

/-! ## The distinguished elements of the model -/

/-- The stable letter, as an element of the model. -/
noncomputable def tauModel : Model := ⟨Tunit Binary.L, Binary.Tunit_mem_elementaryGroup⟩

/-- The mark `e₄₅(1)`, as an element of the model.  Phrased with
`elementaryRoot` rather than `elementaryUnit`: the former is the subtype
element, and it is the shape the Steinberg transport lands in. -/
noncomputable def markModel : Model := elementaryRoot (4 : Fin 16) 5 (by decide) 1

/-- The defect `e₀₂(q)`, as an element of the model. -/
noncomputable def defectModel : Model :=
  elementaryRoot (0 : Fin 16) 2 (by decide) Binary.L.p1

/-- The defect is nontrivial in the model, so nothing below is vacuous. -/
theorem defectModel_ne_one : defectModel ≠ 1 := by
  intro h
  refine Binary.defect_ne_one (by decide) ?_
  have hval := congrArg
    (fun x : Model => (x : (Matrix (Fin 16) (Fin 16) Binary.R)ˣ)) h
  simpa [defectModel] using hval

/-- **Model saturation.**  The defect normally generates the model.  This is
the shortcut applied where it is valid: `normalClosure_root_eq_top` transported
along the Steinberg-to-elementary projection, with rank `16 ≥ 5` and `q ≠ 0`
discharged inside `normalClosure_defect_eq_top`. -/
theorem normalClosure_defectModel_eq_top :
    Subgroup.normalClosure ({defectModel} : Set Model) = ⊤ :=
  normalClosure_defect_eq_top (by decide)

/-! ## The imposed relators -/

/-- The compression `α` of the model: conjugation by the stable letter. -/
noncomputable def alphaModel (g : Model) : Model := tauModel * g * tauModel⁻¹

/-- The compression relator for generator `i`: `τ xᵢ τ⁻¹ = α(xᵢ)`, as a word. -/
noncomputable def compressionRelator (i : Fin generatorCount) :
    FreeGroup (Fin generatorCount) :=
  liftWord tauModel * FreeGroup.of i * (liftWord tauModel)⁻¹ *
    (liftWord (alphaModel (freeToModel (FreeGroup.of i))))⁻¹

/-- The defect word. -/
noncomputable def defectWord : FreeGroup (Fin generatorCount) :=
  liftWord defectModel

/-- A formal product of conjugates of the defect word, indexed by a list of
conjugators together with a sign. -/
noncomputable def conjProduct (l : List (FreeGroup (Fin generatorCount) × Bool)) :
    FreeGroup (Fin generatorCount) :=
  (l.map fun p => p.1 * (if p.2 then defectWord else defectWord⁻¹) * p.1⁻¹).prod

/-- **The open input of this module.**  Model saturation in *word* form: every
model element is the image of a formal product of conjugates of the defect.

This is `normalClosure_defectModel_eq_top` unfolded through
`freeToModel_surjective` by closure induction over `Subgroup.normalClosure`.
It is the single mathematical residual of the cover layer; everything below is
stated relative to it rather than assuming it silently. -/
structure CoverInputs where
  /-- Every model element is the image of a product of conjugates of the
  defect word. -/
  exists_conjProduct : ∀ g : Model,
    ∃ l : List (FreeGroup (Fin generatorCount) × Bool),
      freeToModel (conjProduct l) = g

variable (C : CoverInputs)

/-- The chosen defect expansion of a model element. -/
noncomputable def defectExpansion (g : Model) : FreeGroup (Fin generatorCount) :=
  conjProduct (Classical.choose (C.exists_conjProduct g))

/-- The defect expansion is correct in the model, by construction. -/
theorem freeToModel_defectExpansion (g : Model) :
    freeToModel (defectExpansion C g) = g :=
  Classical.choose_spec (C.exists_conjProduct g)

/-- The saturation relator for generator `i`: `xᵢ = V_{xᵢ}(d)`. -/
noncomputable def saturationRelator (i : Fin generatorCount) :
    FreeGroup (Fin generatorCount) :=
  FreeGroup.of i * (defectExpansion C (freeToModel (FreeGroup.of i)))⁻¹

/-- All imposed relators: the transported cover relators, the compression
family, and the saturation family. -/
noncomputable def relators : Finset (FreeGroup (Fin generatorCount)) :=
  coverRelators ∪ Finset.univ.image compressionRelator ∪
    Finset.univ.image (saturationRelator C)

/-! ## The cover group -/

/-- The Hilbert-hotel cover group. -/
noncomputable abbrev CoverGroup : Type :=
  PresentedGroup ((relators C : Finset (FreeGroup (Fin generatorCount))) :
    Set (FreeGroup (Fin generatorCount)))

instance coverGroup_finitelyPresented :
    Group.IsFinitelyPresented (CoverGroup C) := inferInstance

/-- The cover group is countable, being a quotient of a free group on finitely
many generators. -/
instance coverGroup_countable : Countable (CoverGroup C) :=
  Quotient.mk''_surjective.countable

/-- The word map into the cover group. -/
noncomputable abbrev wordInCoverGroup :
    FreeGroup (Fin generatorCount) →* CoverGroup C :=
  PresentedGroup.mk _

/-- The defect, in the cover group. -/
noncomputable def defect : CoverGroup C := wordInCoverGroup C defectWord

/-! ## The Kazhdan domain and the compression datum -/

/-- The Kazhdan domain: the rank-four corner, `E₄(R)`.  This is
`UniversalRankFour.Ambient` on the nose, so its property `(T)` is the in-repo
`ambient_hasKazhdanPropertyT`, and it is the domain of `cornerEmbedding`. -/
noncomputable abbrev Gamma : Type := ↥UniversalRankFour.Ambient

theorem gamma_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} Gamma :=
  UniversalRankFour.ambient_hasKazhdanPropertyT

/-- The compression datum's `ι`: the block layer's corner embedding of the
rank-four frame into the `16` frame. -/
noncomputable def iota : Gamma →* Model := cornerEmbedding

/-! ## The residual facts about the cover group

Each field below is an open leaf.  They are grouped rather than asserted
individually so that a theorem consuming several of them takes one argument,
and so that discharging one is a local edit.  All of them are downstream of
`CoverInputs`, which is why this structure is parameterized by `C`. -/

structure CoverResiduals where
  /-- Every imposed relator dies in the model, so the covering map factors
  through the cover group.  Three families: the transported cover relators,
  the compression family, and the saturation family (by
  `freeToModel_defectExpansion`).

  The compression family costs nothing: `alphaModel` is *defined* as
  conjugation by `tauModel`, so `compressionRelator i` is
  `τ xᵢ τ⁻¹ · (τ xᵢ τ⁻¹)⁻¹` once pushed through `freeToModel`, and it
  vanishes formally rather than by any fact about the block layer.
  `Tunit_conj_corner` is not what kills it; it is what the
  `tau_compresses` clause below cashes, where the point is not that
  conjugation by `τ` is a map but that it carries the *corner image* back
  into itself. -/
  relator_vanishes : ∀ r ∈ (relators C : Set (FreeGroup (Fin generatorCount))),
    freeToModel r = 1
  /-- A formal product of conjugates of the defect lands in the normal closure
  of the defect.  List induction over `conjProduct`. -/
  conjProduct_mem : ∀ l : List (FreeGroup (Fin generatorCount) × Bool),
    wordInCoverGroup C (conjProduct l) ∈
      Subgroup.normalClosure ({defect C} : Set (CoverGroup C))
  /-- The cover group inherits property `(T)` from `Δ`, being a further
  quotient of it. -/
  kazhdan : HasKazhdanPropertyT.{0, 0} (CoverGroup C)
  /-- The defect survives into the cover group, because its image in the model
  is `defectModel ≠ 1`. -/
  defect_ne_one : defect C ≠ 1
  /-- The compression square: conjugation by `τ` carries the corner image into
  itself, with coefficient map `α(a) = s₀ a t₀`.  This is `Tunit_conj_corner`
  read through `cornerUnits_elementaryUnit`. -/
  tau_compresses : ∀ γ : Gamma, ∃ δ : Gamma,
    tauModel * iota γ * tauModel⁻¹ = iota δ
  /-- The mark centralizes the whole corner image.  This is
  `cornerUnits_commute_mark` at the subgroup level. -/
  mark_commutes : ∀ γ : Gamma, Commute markModel (iota γ)
  /-- The compression core carried by the cover group, assembled from the four
  clauses above. -/
  core : KazhdanCompressionCore Gamma (CoverGroup C)
  /-- **Saturation in the cover group.**  The imposed saturation relators put
  every generator in the normal closure of the defect, via `conjProduct_mem`
  at each generator.  Note this is a statement about the cover, NOT inherited
  from `normalClosure_defectModel_eq_top`: normal closures push forward along
  `CoverGroup ↠ Model` only. -/
  normalClosure_defect_eq_top :
    Subgroup.normalClosure ({defect C} : Set (CoverGroup C)) = ⊤
  /-- The defect of the core is all of the cover group. -/
  top_le_defectNormal : (⊤ : Subgroup (CoverGroup C)) ≤ core.defectNormal

/-- **Saturation in the cover group**, projected from the residuals. -/
theorem defectNormal_eq_top (R : CoverResiduals C) :
    Subgroup.normalClosure ({defect C} : Set (CoverGroup C)) = ⊤ :=
  R.normalClosure_defect_eq_top

/-- The cover group is nontrivial. -/
theorem coverGroup_nontrivial (R : CoverResiduals C) : Nontrivial (CoverGroup C) :=
  ⟨⟨defect C, 1, R.defect_ne_one⟩⟩

/-- Property `(T)` for the whole group, read as a subgroup. -/
theorem top_hasKazhdanPropertyT (R : CoverResiduals C) :
    HasKazhdanPropertyT.{0, 0} ↥(⊤ : Subgroup (CoverGroup C)) :=
  HasKazhdanPropertyT.of_mulEquiv Subgroup.topEquiv R.kazhdan

/-- **The assembly.**  Feeding the compression core to the normal-Kazhdan
criterion at `K = ⊤` gives the full MF residual: the cover group is not
operator MF. -/
theorem not_isOperatorMF_coverGroup (R : CoverResiduals C) :
    ¬ IsOperatorMF (CoverGroup C) := by
  haveI : Nontrivial (CoverGroup C) := coverGroup_nontrivial C R
  exact QuestionTwoReduction.not_isOperatorMF_of_nontrivial_normal_kazhdan_defect
    R.core ⊤ (top_hasKazhdanPropertyT C R) R.top_le_defectNormal top_ne_bot

end Cover
end HilbertHotel
end GroupApproximation
