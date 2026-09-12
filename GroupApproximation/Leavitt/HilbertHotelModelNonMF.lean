import GroupApproximation.Leavitt.HilbertHotelCover
import GroupApproximation.Leavitt.GeneralCornerTheorem
import GroupApproximation.Algebra.GroupTorsionFree
import GroupApproximation.Sofic.FiniteOrderNormalGenerator
import GroupApproximation.Sofic.CDEMFRadical

/-!
# The Hilbert-hotel model is not operator MF

`GroupApproximation.Leavitt.HilbertHotelCover` builds a finitely presented
Shalom cover above the model `E₁₆(L_{𝔽₂}(1,2))`, and lists in `CoverResiduals`
the facts that layer still owes.  Two of those clauses -- the compression
square `τ ι(Γ) τ⁻¹ ⊆ ι(Γ)` and the centralizing mark `[c, ι(Γ)] = 1` -- are
statements about the **model**, not about the cover, and this file discharges
them outright.  Nothing here is stated relative to `CoverInputs` or
`CoverResiduals`: every declaration below is unconditional.

## The one missing computation

The block layer proves the compression square only on *elementary generators*
(`Tunit_conj_corner`, which is `compression_elementary` transported through
`flat16`).  The compression datum wants it on the whole corner image, and the
statement it wants is not a closure induction over `Tunit_conj_corner`: on a
general corner unit `u` the coefficient map is not `a ↦ s₀ a t₀` but

`u ↦ q·I + (s₀·I) u (t₀·I) = matrixCompression u`,

the extra idempotent `q = p₁` being exactly what makes the formula unital and
hence multiplicative.  `HilbertHotelBlocks.compression` already computes
`U · diag(u, I) · V` in that form for an arbitrary block `u`, and its right-hand
side is literally `LeavittFamily.matrixCompression`; `T16_conj` transports it
from the `2m` frame to the `4m` frame at an arbitrary `Y`, and `flat16` carries
it to `M₁₆(R)`.  So `Tunit_conj_cornerUnits` below is the general conjugation
identity, and `Tunit_conj_corner` is its restriction to elementary generators.

## The staging endpoint

With those two clauses the compression core `⟨ι, τ, c, (T), compresses, comm⟩`
exists on the model, and its Hilbert-hotel defect `e₀₂(q)` is universally
Hilbert--Schmidt invisible.  That defect is an involution and normally
generates the model.  The finite-order normal-generator theorem therefore
upgrades its HS invisibility directly to full MF invisibility.  Property `(T)`
is used only for the compressed rank-four group `Gamma` in `modelCore`, not as
a hypothesis on the ambient model in the MF-radical conversion.

What the model does **not** have is finite presentability: `Model` is
`EL₁₆(L_{𝔽₂}(1,2))`, which the development gives as a matrix group, not by a
finite presentation.  Supplying that is exactly the job of the cover layer, and
is why `HilbertHotelCover` exists at all.  The results below are therefore a
staging post: the analytic obstruction is already unconditional here, and only
the finiteness of the presentation is still owed downstream.
-/

namespace GroupApproximation
namespace HilbertHotel

open scoped commutatorElement

/-! ## The corner compression, on arbitrary units

`LeavittFamily.matrixCompression` and the block-frame right-hand side of
`HilbertHotelBlocks.compression` are the same formula written twice: the
former with `LeavittFamily.scalarDiagonal`, the latter with `Matrix.scalar`,
and with the two summands in the opposite order. -/

section Compression

variable {R : Type*} [Ring R]

/-- The block-frame compression formula is `LeavittFamily.matrixCompression`.
Both sides are `q·I + (s₀·I) M (t₀·I)`; the two spellings of a constant
diagonal matrix are reconciled entrywise. -/
theorem matrixCompression_eq_scalar_form (L : LeavittFamily R)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ R) :
    Matrix.scalar κ L.s0 * M * Matrix.scalar κ L.t0 + Matrix.scalar κ L.p1
      = L.matrixCompression M := by
  ext i j
  rw [Matrix.add_apply, scalar_mul_mul_scalar, Matrix.of_apply,
    LeavittFamily.matrixCompression_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  exact add_comm _ _

/-- **Conjugation compresses the whole corner block.**  The Whitehead matrix
carries `diag(M, I₄, I₄, I₄)` to `diag(matrixCompression M, I₄, I₄, I₄)`.

This is the general form of `Tunit_conj_corner`, whose coefficient map
`a ↦ s₀ a t₀` is the *additive* shadow of the formula: on a general block the
complementary idempotent `q` survives, and it must, since a unital map is what
is needed on units. -/
theorem T_conj_cornerBlock (L : LeavittFamily R) (M : Matrix (Fin 4) (Fin 4) R) :
    T L * cornerBlock M * Tinv L = cornerBlock (L.matrixCompression M) := by
  unfold cornerBlock T Tinv
  rw [← map_mul, ← map_mul, T16_conj, compression, matrixCompression_eq_scalar_form]

/-- **The compression square of the datum.**  Conjugation by the stable letter
carries the corner copy `ι(GL₄(R)) ≤ GL₁₆(R)` into itself, implementing
`LeavittFamily.matrixCompressionUnit` on coefficients. -/
theorem Tunit_conj_cornerUnits (L : LeavittFamily R) (u : (Matrix (Fin 4) (Fin 4) R)ˣ) :
    Tunit L * cornerUnits u * (Tunit L)⁻¹ = cornerUnits (L.matrixCompressionUnit u) := by
  apply Units.ext
  show T L * cornerBlock (u : Matrix (Fin 4) (Fin 4) R) * Tinv L
    = cornerBlock (L.matrixCompression (u : Matrix (Fin 4) (Fin 4) R))
  exact T_conj_cornerBlock L _

end Compression

/-! ## Two corner indices

`corner` is the identity on values, so the corner images of `1` and `2` are the
`16`-frame indices `1` and `2`.  These are needed to recognise the corner
generator `e₁₂(1)` -- the second argument of the defect commutator -- as the
image of a rank-four element. -/

theorem corner_one_eq : corner (1 : Fin 4) = (1 : Fin 16) := by decide

theorem corner_two_eq : corner (2 : Fin 4) = (2 : Fin 16) := by decide

namespace Cover

/-! ## The two model-level clauses of `CoverResiduals`

`tau_compresses` and `mark_commutes` are stated exactly as the corresponding
fields of `CoverResiduals`, so each discharges its field by name. -/

/-- **The compression square, at the model.**  The stable letter `τ = Tunit L`
conjugates the corner image `ι(Γ)` into itself; the witness is the corner
compression endomorphism of `EL₄(R)`, whose membership in the elementary group
is `matrixCompressionHom_mem_elementary`. -/
theorem tau_compresses (γ : Gamma) :
    ∃ δ : Gamma, tauModel * iota γ * tauModel⁻¹ = iota δ := by
  refine ⟨LeavittFamily.elementaryCompressionEnd (ι := Fin 4) Binary.L γ, ?_⟩
  apply Subtype.ext
  show Tunit Binary.L * cornerUnits (γ : (Matrix (Fin 4) (Fin 4) Binary.R)ˣ)
        * (Tunit Binary.L)⁻¹
    = cornerUnits
        (Binary.L.matrixCompressionUnit (γ : (Matrix (Fin 4) (Fin 4) Binary.R)ˣ))
  exact Tunit_conj_cornerUnits Binary.L _

/-- **The mark centralizes the corner image, at the model.**  This is
`cornerUnits_commute_mark` read through the two definitional identifications
`elementaryRoot_val` and `cornerEmbedding_apply`. -/
theorem mark_commutes (γ : Gamma) : Commute markModel (iota γ) := by
  rw [commute_iff_eq]
  apply Subtype.ext
  exact ((cornerUnits_commute_mark (R := Binary.R) (by decide)
    (γ : (Matrix (Fin 4) (Fin 4) Binary.R)ˣ) γ.property).symm).eq

/-! ## The compression core carried by the model -/

/-- **The model's compression core.**  All four clauses are unconditional:
property `(T)` for the rank-four ambient group is `ambient_hasKazhdanPropertyT`,
the compression square is `tau_compresses`, and the centralizing mark is
`mark_commutes`. -/
noncomputable def modelCore : KazhdanCompressionCore Gamma Model where
  iota := iota
  t := tauModel
  c := markModel
  kazhdan := gamma_hasKazhdanPropertyT
  compresses := tau_compresses
  comm_c := mark_commutes

/-! ## The defect lies in the core's defect

The defect of the construction is `e₀₂(q)`, and `defect_from_conjugated_mark`
exhibits it as the commutator of the transported mark against the corner
generator `e₁₂(1)`.  That generator is `ι` of a rank-four element, which is
what puts the defect in `defectSet` rather than merely near it. -/

/-- The rank-four element whose corner image is the model root `e₁₂(1)`. -/
noncomputable def cornerGenerator : Gamma := elementaryRoot (1 : Fin 4) 2 (by decide) 1

/-- Its image in the model is the `16`-frame root `e₁₂(1)`. -/
theorem iota_cornerGenerator_val :
    ((iota cornerGenerator : Model) : (Matrix (Fin 16) (Fin 16) Binary.R)ˣ)
      = elementaryUnit (1 : Fin 16) 2 (by decide) 1 := by
  show cornerUnits (elementaryUnit (1 : Fin 4) 2 (by decide) (1 : Binary.R))
    = elementaryUnit (1 : Fin 16) 2 (by decide) 1
  rw [cornerUnits_elementaryUnit]
  apply Units.ext
  show (1 : Matrix (Fin 16) (Fin 16) Binary.R)
      + Matrix.single (corner (1 : Fin 4)) (corner (2 : Fin 4)) 1
    = 1 + Matrix.single (1 : Fin 16) 2 1
  rw [corner_one_eq, corner_two_eq]

/-! The commutator identity is assembled by *rewriting* the model-level values
into place, never by asking the elaborator to normalize
`⁅modelCore.transported, modelCore.iota cornerGenerator⁆` definitionally.  That
term carries the whole `Subtype`/`Units`/`Matrix` coercion tower over
`L_{𝔽₂}(1,2)` at once, and normalizing it is a heartbeat sink; each of the
small `rfl` steps below crosses exactly one layer of it. -/

/-- The stable letter, in the unit group. -/
@[simp] theorem tauModel_val :
    ((tauModel : Model) : (Matrix (Fin 16) (Fin 16) Binary.R)ˣ) = Tunit Binary.L := rfl

/-- The mark, in the unit group. -/
@[simp] theorem markModel_val :
    ((markModel : Model) : (Matrix (Fin 16) (Fin 16) Binary.R)ˣ)
      = elementaryUnit (4 : Fin 16) 5 (by decide) 1 := rfl

/-- The defect, in the unit group. -/
@[simp] theorem defectModel_val :
    ((defectModel : Model) : (Matrix (Fin 16) (Fin 16) Binary.R)ˣ)
      = elementaryUnit (0 : Fin 16) 2 (by decide) Binary.L.p1 := rfl

/-- The transported root of the core is `τ c τ⁻¹`.  Stated at the model level,
so that no coercion is unfolded at this step. -/
@[simp] theorem modelCore_transported_eq :
    modelCore.transported = tauModel * markModel * tauModel⁻¹ := rfl

/-- The corner generator's image, at the model level. -/
theorem modelCore_iota_cornerGenerator_eq :
    modelCore.iota cornerGenerator = elementaryRoot (1 : Fin 16) 2 (by decide) 1 := by
  apply Subtype.ext
  exact iota_cornerGenerator_val

/-- **The defect is a pointwise compression defect.**  Commuting the
transported mark `τ c τ⁻¹` against `ι(e₁₂(1))` gives exactly `e₀₂(q)`. -/
theorem transported_commutator_eq_defect :
    ⁅modelCore.transported, modelCore.iota cornerGenerator⁆ = defectModel := by
  have hdef := Binary.defect_from_conjugated_mark
    (by decide) (by decide) (by decide) (by decide)
  rw [commutatorElement_def] at hdef
  rw [modelCore_transported_eq, modelCore_iota_cornerGenerator_eq, commutatorElement_def]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, tauModel_val, markModel_val,
    defectModel_val, elementaryRoot_val]
  exact hdef

theorem defectModel_mem_defectNormal : defectModel ∈ modelCore.defectNormal := by
  rw [← transported_commutator_eq_defect]
  exact modelCore.defect_mem_defectNormal cornerGenerator

/-! ## The staging endpoint -/

/-- The rank-sixteen elementary model is finitely generated directly from its
finite-type coefficient algebra.  No ambient property-`(T)` input is used. -/
theorem model_fg : Group.FG Model :=
  elementaryGroup_finitelyGenerated 16 (by omega)

noncomputable local instance model_fg_instance : Group.FG Model := model_fg

/-- The model is countable because it is finitely generated. -/
instance model_countable : Countable Model := countable_of_fg model_fg

/-- The model is nontrivial, because the defect is. -/
theorem model_nontrivial : Nontrivial Model :=
  ⟨⟨defectModel, 1, defectModel_ne_one⟩⟩

/-- The normally generating Hilbert-hotel defect is an involution.  This is
the characteristic-two elementary-root relation, recorded here because it
completely determines what happens under maps to torsion-free groups. -/
theorem defectModel_sq : defectModel ^ 2 = 1 := by
  exact elementaryRoot_pow_char 2 (0 : Fin 16) 2 (by decide) Binary.L.p1

/-- The nontrivial Hilbert-hotel defect has finite order (indeed order two). -/
theorem defectModel_isOfFinOrder : IsOfFinOrder defectModel :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, defectModel_sq⟩

/-- **The Hilbert-hotel model has no nontrivial torsion-free image.**  Its
normally generating defect has order two, so every map to a torsion-free
group kills that defect and hence its whole normal closure.  Thus the
unconditional full-MF-radical model cannot be converted into the requested
torsion-free witness by taking its universal torsion-free quotient. -/
theorem hom_eq_one_to_isPowerTorsionFree
    {T : Type*} [Group T] (hT : IsPowerTorsionFree T) (f : Model →* T) :
    f = 1 := by
  have hdef : f defectModel = 1 := by
    apply hT (f defectModel) 2 (by decide)
    rw [← map_pow, defectModel_sq, map_one]
  have hclosure : Subgroup.normalClosure ({defectModel} : Set Model) ≤ f.ker := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact MonoidHom.mem_ker.mpr hdef
  apply MonoidHom.ext
  intro g
  apply MonoidHom.mem_ker.mp
  apply hclosure
  rw [normalClosure_defectModel_eq_top]
  exact Subgroup.mem_top g

/-- In particular the model itself is not torsion-free. -/
theorem model_not_isPowerTorsionFree : ¬ IsPowerTorsionFree Model := by
  intro htf
  have htrivial : MonoidHom.id Model = 1 :=
    hom_eq_one_to_isPowerTorsionFree htf (MonoidHom.id Model)
  exact defectModel_ne_one (by
    simpa using DFunLike.congr_fun htrivial defectModel)

/-- The compression core kills the distinguished defect in every normalized
Hilbert--Schmidt ultraproduct arising from an operator-norm almost
representation. -/
theorem defectModel_mem_opToHSShadowResidual :
    defectModel ∈ opToHSShadowResidual Model := by
  rw [mem_opToHSShadowResidual_iff]
  intro B U hcof
  exact modelCore.defectNormal_hyperlinear_killed
    B U hcof defectModel defectModel_mem_defectNormal

/-- **The finite-order bridge at the Hilbert-hotel defect.**  Universal HS
triviality upgrades directly to full MF invisibility because the involution
normally generates the finitely generated ambient model. -/
theorem defectModel_mem_normMFResidual : defectModel ∈ normMFResidual Model :=
  (FiniteOrderNormalGenerator.finiteOrder_normalGenerator_mem_normMFResidual_iff_mem_opToHSShadowResidual
      defectModel_isOfFinOrder normalClosure_defectModel_eq_top).mpr
    defectModel_mem_opToHSShadowResidual

/-- The ultraproduct-language form of the full-radical theorem. -/
theorem normMFResidual_model_eq_top : normMFResidual Model = ⊤ := by
  apply top_unique
  rw [← normalClosure_defectModel_eq_top]
  apply Subgroup.normalClosure_le_normal
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  exact defectModel_mem_normMFResidual

/-- **Full MF radical.**  Every element of the model is invisible in every
standard cofinite norm-matrix corona. -/
theorem coronaMFResidual_model_eq_top : coronaMFResidual Model = ⊤ := by
  rw [coronaMFResidual_eq_normMFResidual]
  exact normMFResidual_model_eq_top

/-- **The model is not operator MF.**  Its nontrivial normally generating
involution lies in the MF residual, so that residual is the whole group. -/
theorem not_isOperatorMF_model : ¬ IsOperatorMF Model := by
  haveI : Nontrivial Model := model_nontrivial
  intro hMF
  have hbot := normMFResidual_eq_bot_of_isOperatorMF hMF
  rw [normMFResidual_model_eq_top] at hbot
  exact top_ne_bot hbot

/-- **The literal Carrión--Dadarlat--Eckhardt full radical.**  Every
homomorphism of the model into the unitary group of a genuine norm-matrix
C-star corona is trivial. -/
theorem cdeMFResidual_model_eq_top : cdeMFResidual Model = ⊤ := by
  rw [cdeMFResidual_eq_coronaMFResidual]
  exact coronaMFResidual_model_eq_top

/-- The literal CDE form of the negative conclusion. -/
theorem not_isCDEOperatorMF_model : ¬ IsCDEOperatorMF Model := by
  haveI : Nontrivial Model := model_nontrivial
  rw [isCDEOperatorMF_iff_cdeMFResidual_eq_bot, cdeMFResidual_model_eq_top]
  exact top_ne_bot

end Cover
end HilbertHotel
end GroupApproximation
