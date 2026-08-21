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
`HilbertHotelWhitehead`, `HilbertHotelBinary`) supplies, inside the elementary
group `E₁₆(R)` over `R = L_{𝔽₂}(1,2)`:

* a stable letter `τ = Tunit L`, elliptic (`Tunit_mem_elementaryGroup`), whose
  conjugation compresses the rank-four corner copy of `E₄(R)` by
  `a ↦ s₀ a t₀` (`Tunit_conj_corner`);
* a mark `c = e₄₅(1)` centralizing that corner (`cornerUnits_commute_mark`) --
  the reason is index-disjointness of the two *root positions*, both corner
  indices being `< 4` against `(4,5)`, not block-disjointness as such: two
  roots in different blocks can still chain if one's column meets the other's
  row, and the proof cashes exactly `corner j ≠ 4` and `5 ≠ corner i`;
* a defect `d = e₀₂(q)` with `q = p₁ = s₁t₁` full and nonzero
  (`defect_from_conjugated_mark`, `defect_ne_one`, `q_ne_zero`).

This file sits above that layer and builds the *cover presentation*: a
finitely presented Kazhdan group `CoverGroup` whose compression defect is all
of it, ready for the normal-Kazhdan criterion at `K = ⊤`.

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
a statement about `St_n(R)` and does *not* transfer backwards along
`CoverGroup ↠ image`: a surjection gives `⟨⟨d⟩⟩ · ker = ⊤`, not `⟨⟨d⟩⟩ = ⊤`.
So on this route the saturation relators must be **imposed**, one per
generator, and the block identities become the *consistency* input that proves
the imposed relators are true in the model rather than the source of the
saturation itself.

Imposing them needs explicit words, not mere membership, which is exactly what
`saturation_chain` gives at one root position and what the pending
`saturation_chain_generic` will give at every index quadruple.  That is the
single open leaf of this file.
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

/-! ## The imposed relators

Three families, all finite.  The compression relators transport the corner
compression; the defect-identification relator names the defect; the
saturation relators express each generator as a word in conjugates of the
defect, which is what forces `⟨⟨d⟩⟩ = ⊤` in the quotient. -/

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

/-- **The open leaf.**  An explicit word expressing the model element `g` as a
product of conjugates of the defect.

**How the shortcut actually applies.**  hh1 and the coordinator both point at
`BinaryLeavittSteinberg.normalClosure_root_eq_top` as the way to avoid a Weyl
argument, and they are right that no Weyl argument is needed -- but not because
that theorem gives `defectNormal = ⊤` up here.  It cannot: it is a statement
about `St_n(R)`, and along `CoverGroup ↠ Model` a normal closure only pushes
*forward*, giving `⟨⟨d⟩⟩ · ker = ⊤` rather than `⟨⟨d⟩⟩ = ⊤`.

What it does give is the **words**.  Saturation in the model says every model
element is *some* product of conjugates of the defect; choosing such a product
(non-constructively, exactly as `liftWord` chooses a preimage) yields the
relator `xᵢ = V_{xᵢ}(d)` we impose, and imposing it is what makes
`⟨⟨d⟩⟩ = ⊤` true in `CoverGroup` by construction.  So the shortcut removes the
need for explicit words from `saturation_chain_generic`, and the direction
error is avoided by keeping the relators imposed.
-/
theorem normalClosure_defectModel_eq_top :
    Subgroup.normalClosure ({defectModel} : Set Model) = ⊤ :=
  normalClosure_defect_eq_top (by decide)

/-- A formal product of conjugates of the defect word, indexed by a list of
conjugators together with a sign. -/
noncomputable def conjProduct (l : List (FreeGroup (Fin generatorCount) × Bool)) :
    FreeGroup (Fin generatorCount) :=
  (l.map fun p => p.1 * (if p.2 then defectWord else defectWord⁻¹) * p.1⁻¹).prod

/-- **Model saturation, in word form.**  Every model element is the image of a
formal product of conjugates of the defect.  This is
`normalClosure_defectModel_eq_top` unfolded through `freeToModel_surjective`
by closure induction; it is the single mathematical leaf of this file. -/
theorem exists_conjProduct (g : Model) :
    ∃ l : List (FreeGroup (Fin generatorCount) × Bool),
      freeToModel (conjProduct l) = g := by
  sorry

/-- The chosen defect expansion of a model element. -/
noncomputable def defectExpansion (g : Model) : FreeGroup (Fin generatorCount) :=
  conjProduct (Classical.choose (exists_conjProduct g))

/-- The defect expansion is correct in the model, by construction. -/
theorem freeToModel_defectExpansion (g : Model) :
    freeToModel (defectExpansion g) = g :=
  Classical.choose_spec (exists_conjProduct g)

/-- The saturation relator for generator `i`: `xᵢ = V_{xᵢ}(d)`. -/
noncomputable def saturationRelator (i : Fin generatorCount) :
    FreeGroup (Fin generatorCount) :=
  FreeGroup.of i * (defectExpansion (freeToModel (FreeGroup.of i)))⁻¹

/-- All imposed relators: the transported cover relators, the compression
family, and the saturation family. -/
noncomputable def relators : Finset (FreeGroup (Fin generatorCount)) :=
  coverRelators ∪ Finset.univ.image compressionRelator ∪
    Finset.univ.image saturationRelator

/-! ## The cover group -/

/-- The Hilbert-hotel cover group. -/
noncomputable abbrev CoverGroup : Type :=
  PresentedGroup ((relators : Finset (FreeGroup (Fin generatorCount))) :
    Set (FreeGroup (Fin generatorCount)))

instance coverGroup_finitelyPresented : Group.IsFinitelyPresented CoverGroup :=
  inferInstance

/-- The word map into the cover group. -/
noncomputable abbrev wordInCoverGroup :
    FreeGroup (Fin generatorCount) →* CoverGroup :=
  PresentedGroup.mk _

/-- `CoverGroup` is a quotient of `Δ`, so it inherits property `(T)`. -/
theorem coverGroup_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} CoverGroup := by
  sorry

/-! ## Consistency: the surjection onto the model

Every imposed relator dies in the model, so the covering map factors through
`CoverGroup`.  This is what keeps the quotient nontrivial: the defect survives
because its image `e₀₂(q)` is nontrivial by `defect_ne_one`. -/

/-- Each imposed relator maps to the identity of the model. -/
theorem freeToModel_relator_eq_one {r : FreeGroup (Fin generatorCount)}
    (hr : r ∈ (relators : Set (FreeGroup (Fin generatorCount)))) :
    freeToModel r = 1 := by
  sorry

/-- **The consistency surjection.** -/
noncomputable def toModel : CoverGroup →* Model :=
  PresentedGroup.toGroup (f := fun i => freeToModel (FreeGroup.of i))
    (fun _ hr => by
      sorry)

theorem toModel_surjective : Function.Surjective toModel := by
  sorry

/-! ## The defect and its saturation -/

/-- The defect, in the cover group. -/
noncomputable def defect : CoverGroup := wordInCoverGroup defectWord

/-- The defect is nontrivial, because its image in the model is. -/
theorem defect_ne_one : defect ≠ 1 := by
  sorry

/-- A formal product of conjugates of the defect word lands in the normal
closure of the defect.  This is the half that makes the imposed saturation
relators do their job. -/
theorem wordInCoverGroup_conjProduct_mem
    (l : List (FreeGroup (Fin generatorCount) × Bool)) :
    wordInCoverGroup (conjProduct l) ∈
      Subgroup.normalClosure ({defect} : Set CoverGroup) := by
  sorry

/-- The chosen defect expansion lands in the normal closure of the defect, by
construction.  Applied at each generator, this is what makes
`defectNormal_eq_top` hold. -/
theorem defectExpansion_mem_normalClosure (g : Model) :
    wordInCoverGroup (defectExpansion g) ∈
      Subgroup.normalClosure ({defect} : Set CoverGroup) :=
  wordInCoverGroup_conjProduct_mem _

/-- **Saturation.**  The saturation relators put every generator in the normal
closure of the defect, so the defect normally generates the cover group. -/
theorem defectNormal_eq_top :
    Subgroup.normalClosure ({defect} : Set CoverGroup) = ⊤ := by
  sorry

/-- The cover group is nontrivial. -/
theorem coverGroup_nontrivial : Nontrivial CoverGroup :=
  ⟨⟨defect, 1, defect_ne_one⟩⟩

/-! ## Assembly

The compression datum in the shape `QuestionTwoReduction` consumes, with the
rank-four corner as the Kazhdan domain `Γ`, the stable letter as `t`, and the
mark as `c`.  Feeding it at `K = ⊤` needs three bridges beyond
`defectNormal_eq_top`: `(⊤ : Subgroup CoverGroup)` is Kazhdan (transport
`coverGroup_hasKazhdanPropertyT` along `Subgroup.topEquiv` with
`HasKazhdanPropertyT.of_mulEquiv`), `⊤ ≠ ⊥` (from `coverGroup_nontrivial`), and
`⊤ ≤ defectNormal`. -/

/-- The Kazhdan domain: the rank-four corner, `E₄(R)`.  This is
`UniversalRankFour.Ambient` on the nose, so its property `(T)` is the in-repo
`ambient_hasKazhdanPropertyT`. -/
noncomputable abbrev Gamma : Type := ↥UniversalRankFour.Ambient

theorem gamma_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} Gamma :=
  UniversalRankFour.ambient_hasKazhdanPropertyT

/-- The compression datum's `ι`: the block layer's corner embedding of the
rank-four frame into the `16` frame. -/
noncomputable def iota : Gamma →* Model := cornerEmbedding

/-- **The compression square.**  Conjugation by the stable letter carries the
corner copy into itself, with coefficient map `α(a) = s₀ a t₀` on the
rank-four side.  This is `Tunit_conj_corner` read through
`cornerUnits_elementaryUnit`, and it is the
`τ · ι(Λ) · τ⁻¹ ⊆ ι(Λ)` clause of the compression datum. -/
theorem tau_compresses_iota (γ : Gamma) :
    ∃ δ : Gamma, tauModel * iota γ * tauModel⁻¹ = iota δ := by
  sorry

/-- **The centralizing clause.**  The mark commutes with the whole corner
image, not merely with individual generators.  This is hh1's
`cornerUnits_commute_mark` read at the subgroup level, and it is the
`[c, ι(Λ)] = 1` clause of the compression datum. -/
theorem mark_commutes_iota (γ : Gamma) : Commute markModel (iota γ) := by
  sorry

/-- The compression core carried by the cover group. -/
noncomputable def compressionCore : KazhdanCompressionCore Gamma CoverGroup := by
  sorry

/-- Property `(T)` for the whole group, read as a subgroup. -/
theorem top_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} ↥(⊤ : Subgroup CoverGroup) :=
  HasKazhdanPropertyT.of_mulEquiv Subgroup.topEquiv coverGroup_hasKazhdanPropertyT

/-- `⊤` is contained in the compression defect. -/
theorem top_le_defectNormal : (⊤ : Subgroup CoverGroup) ≤ compressionCore.defectNormal := by
  sorry

/-- The cover group is countable, being a quotient of a free group on finitely
many generators. -/
instance coverGroup_countable : Countable CoverGroup :=
  Quotient.mk''_surjective.countable

/-- **The assembly.**  Feeding the compression core to the normal-Kazhdan
criterion at `K = ⊤` gives the full MF residual: no nontrivial quotient of the
cover group is operator MF. -/
theorem not_isOperatorMF_coverGroup : ¬ IsOperatorMF CoverGroup := by
  haveI : Nontrivial CoverGroup := coverGroup_nontrivial
  exact QuestionTwoReduction.not_isOperatorMF_of_nontrivial_normal_kazhdan_defect
    compressionCore ⊤ top_hasKazhdanPropertyT top_le_defectNormal top_ne_bot

end Cover
end HilbertHotel
end GroupApproximation
