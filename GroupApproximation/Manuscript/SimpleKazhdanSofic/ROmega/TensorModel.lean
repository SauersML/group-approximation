import GroupApproximation.Manuscript.SimpleKazhdanSofic.ROmega.TwistedModel
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ROmega.GroupModel
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ROmega.PauliShift
import GroupApproximation.Analysis.McDuffTensorHyperfinite
import GroupApproximation.Meta.AxiomGuard

/-!
# `L(G) ⊗̄ 𝓡 ↪ R^ω` for a countable sofic group

`simple_kazhdan_sofic_group.tex`, subsection "Brown's formulation":

> (tex 350–355) … $L(G)\mathbin{\bar\otimes}\mathcal R \hookrightarrow
> \mathcal R^\omega\mathbin{\bar\otimes}\mathcal R\subseteq(\mathcal R\mathbin{\bar\otimes}
> \mathcal R)^\omega\cong\mathcal R^\omega$.

Route.  Let `σₙ` be a sofic approximation of `G` and `jₙ = stageLevel X n` the Pauli stage that
carries the matrix corner of coordinate `n`.  For a Pauli word `p` put
`[p]' := [shiftOp_{jₙ} p]ₙ ∈ 𝓡^ω`: the word `p` moved past the sites of stage `jₙ`.  These classes
obey the Pauli relations (`shiftOp_mul`, `star_shiftOp`), commute with the image of the matrix
ultraproduct (`commute_shiftOp_stageHom`), and `[p]'·x` has ultratrace `0` for `p ≠ 1`
(`coefficient_shiftOp_mul_stageHom`).  Hence `u(p, g) := [p]'·[σₙ(g)]` is a projective model of
`(P × G, pauliCocycle ⊕ 0)` whose non-identity values have ultratrace `0`, so
`exists_twisted_embedding_of_model` embeds `L_{β ⊕ 0}(P × G)` in `R^ω`.  The spatial isomorphism
`TwistedProduct.curryConj_image_twistedTensor` identifies `L_{β ⊕ 0}(P × G)` with
`L(G) ⊗̄ 𝓡 = McDuff.tensorHyperfinite (L(G))`, which gives `exists_tensorHyperfinite_embedding`.
This realises `𝓡^ω ⊗̄ 𝓡 ⊆ (𝓡 ⊗̄ 𝓡)^ω ≅ 𝓡^ω` concretely, coordinate by coordinate.
-/

namespace GroupApproximation.SimpleKazhdanSofic.ROmega

open TracialUltrapower ReducedGroupCStarTrace TwistedGroupVonNeumann Hyperfinite
open scoped InnerProductSpace

noncomputable section

section Model

variable {G : Type} [Group G] (S : SoficApproximation G) [∀ n, Nonempty (S.model n)]
variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)

/-- The Pauli word `p` shifted past stage `jₙ` in coordinate `n`. -/
def pauliShiftSeq (p : PauliGroup) : boundedSeq hyperfiniteFactor :=
  ⟨fun n ↦ shiftOp (stageLevel (fun n ↦ S.model n) n) p, fun _ ↦ shiftOp_mem _ p, 1,
    fun _ ↦ norm_shiftOp_le _ p⟩

/-- The class `[shiftOp_{jₙ} p]ₙ ∈ 𝓡^ω`. -/
def pauliShiftClass (p : PauliGroup) : HyperfiniteUltrapower ω :=
  TracialUltrapower.mk hyperfiniteTracialVector ω (pauliShiftSeq S p)

theorem pauliShiftClass_one : pauliShiftClass S ω 1 = 1 := by
  have h : pauliShiftSeq S 1 = 1 :=
    Subtype.ext (funext fun n ↦ shiftOp_one (stageLevel (fun n ↦ S.model n) n))
  rw [pauliShiftClass, h, map_one]

theorem pauliShiftClass_mul (p q : PauliGroup) :
    pauliShiftClass S ω p * pauliShiftClass S ω q
      = zsign (pauliCocycle p q) • pauliShiftClass S ω (p * q) := by
  have h : pauliShiftSeq S p * pauliShiftSeq S q
      = zsign (pauliCocycle p q) • pauliShiftSeq S (p * q) :=
    Subtype.ext (funext fun n ↦ shiftOp_mul (stageLevel (fun n ↦ S.model n) n) p q)
  rw [pauliShiftClass, pauliShiftClass, pauliShiftClass,
    ← map_mul (TracialUltrapower.mk hyperfiniteTracialVector ω), h, mk_smul]

theorem star_pauliShiftClass (p : PauliGroup) :
    star (pauliShiftClass S ω p) = zsign (pauliCocycle p p⁻¹) • pauliShiftClass S ω p⁻¹ := by
  have h : star (pauliShiftSeq S p) = zsign (pauliCocycle p p⁻¹) • pauliShiftSeq S p⁻¹ :=
    Subtype.ext (funext fun n ↦ star_shiftOp (stageLevel (fun n ↦ S.model n) n) p)
  rw [pauliShiftClass, pauliShiftClass, star_mk, h, mk_smul]

/-- The shifted words commute with the image of the matrix ultraproduct in `𝓡^ω`. -/
theorem commute_pauliShiftClass_map (p : PauliGroup)
    (x : TracialUltraproduct.TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ)) :
    Commute (pauliShiftClass S ω p)
      (matrixUltraproductToHyperfiniteUltrapower (fun n ↦ S.model n) ω hω x) := by
  obtain ⟨a, rfl⟩ :=
    TracialUltraproduct.tracialMatrixQuotientMk_surjective (fun n ↦ S.model n) (ω : Filter ℕ) x
  rw [matrixUltraproductToHyperfiniteUltrapower_mk, pauliShiftClass]
  have h : pauliShiftSeq S p * seqMap (fun n ↦ S.model n) a
      = seqMap (fun n ↦ S.model n) a * pauliShiftSeq S p := by
    refine Subtype.ext (funext fun n ↦ ?_)
    show shiftOp (stageLevel (fun n ↦ S.model n) n) p
        * stageCorner (stageEmbedding (fun n ↦ S.model n) n) (a n)
      = stageCorner (stageEmbedding (fun n ↦ S.model n) n) (a n)
        * shiftOp (stageLevel (fun n ↦ S.model n) n) p
    rw [stageCorner_apply]
    exact (commute_shiftOp_stageHom p _).eq
  have hc : Commute (pauliShiftSeq S p) (seqMap (fun n ↦ S.model n) a) := h
  exact hc.map (TracialUltrapower.mk hyperfiniteTracialVector ω)

/-- `[p]'·x` has ultratrace `0` for `p ≠ 1` and `x` in the image of the matrix ultraproduct. -/
theorem ultratrace_pauliShiftClass_mul_map {p : PauliGroup} (hp : p ≠ 1)
    (x : TracialUltraproduct.TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ)) :
    hyperfiniteUltratrace ω (pauliShiftClass S ω p
      * matrixUltraproductToHyperfiniteUltrapower (fun n ↦ S.model n) ω hω x) = 0 := by
  obtain ⟨a, rfl⟩ :=
    TracialUltraproduct.tracialMatrixQuotientMk_surjective (fun n ↦ S.model n) (ω : Filter ℕ) x
  have hn : ∀ n, seqTrace hyperfiniteTracialVector
      (pauliShiftSeq S p * seqMap (fun n ↦ S.model n) a) n = 0 := by
    intro n
    show ⟪deltaOne PauliGroup, (shiftOp (stageLevel (fun n ↦ S.model n) n) p
      * stageCorner (stageEmbedding (fun n ↦ S.model n) n) (a n)) (deltaOne PauliGroup)⟫_ℂ = 0
    rw [GroupVonNeumann.inner_deltaOne_left PauliGroup, ← ambientCoefficientAtOne_apply,
      stageCorner_apply, coefficient_shiftOp_mul_stageHom hp]
  have h0 : seqUltratrace hyperfiniteTracialVector ω
      (pauliShiftSeq S p * seqMap (fun n ↦ S.model n) a) = 0 :=
    tendsto_nhds_unique (tendsto_seqUltratrace hyperfiniteTracialVector ω _)
      (Filter.Tendsto.congr (fun n ↦ (hn n).symm) tendsto_const_nhds)
  rw [matrixUltraproductToHyperfiniteUltrapower_mk, pauliShiftClass,
    ← map_mul (TracialUltrapower.mk hyperfiniteTracialVector ω)]
  exact (ultratrace_mk hyperfiniteTracialVector ω _).trans h0

theorem commute_pauliShiftClass_soficHyperfinite (p : PauliGroup) (g : G) :
    Commute (pauliShiftClass S ω p) (soficHyperfinite S ω hω g) := by
  rw [soficHyperfinite]
  exact commute_pauliShiftClass_map S ω hω p _

/-- The projective model `u(p, g) = [p]'·[σₙ(g)]` of `(P × G, pauliCocycle ⊕ 0)`. -/
def pauliSoficModel (x : PauliGroup × G) : HyperfiniteUltrapower ω :=
  pauliShiftClass S ω x.1 * soficHyperfinite S ω hω x.2

theorem pauliSoficModel_one : pauliSoficModel S ω hω 1 = 1 := by
  rw [pauliSoficModel, Prod.fst_one, Prod.snd_one, pauliShiftClass_one, soficHyperfinite_one,
    one_mul]

theorem pauliSoficModel_mul (x y : PauliGroup × G) :
    pauliSoficModel S ω hω x * pauliSoficModel S ω hω y
      = zsign (TwistedProduct.prodCocycle pauliCocycle (fun _ _ : G ↦ (0 : ZMod 2)) x y)
        • pauliSoficModel S ω hω (x * y) := by
  have hc : TwistedProduct.prodCocycle pauliCocycle (fun _ _ : G ↦ (0 : ZMod 2)) x y
      = pauliCocycle x.1 y.1 :=
    add_zero (pauliCocycle x.1 y.1)
  rw [hc, pauliSoficModel, pauliSoficModel, pauliSoficModel, Prod.fst_mul, Prod.snd_mul,
    soficHyperfinite_mul, mul_assoc, ← mul_assoc (soficHyperfinite S ω hω x.2),
    ← (commute_pauliShiftClass_soficHyperfinite S ω hω y.1 x.2).eq,
    mul_assoc (pauliShiftClass S ω y.1), ← mul_assoc, pauliShiftClass_mul, smul_mul_assoc]

theorem star_pauliSoficModel (x : PauliGroup × G) :
    star (pauliSoficModel S ω hω x)
      = zsign (TwistedProduct.prodCocycle pauliCocycle (fun _ _ : G ↦ (0 : ZMod 2)) x x⁻¹)
        • pauliSoficModel S ω hω x⁻¹ := by
  have hc : TwistedProduct.prodCocycle pauliCocycle (fun _ _ : G ↦ (0 : ZMod 2)) x x⁻¹
      = pauliCocycle x.1 x.1⁻¹ :=
    add_zero (pauliCocycle x.1 x.1⁻¹)
  rw [hc, pauliSoficModel, pauliSoficModel, Prod.fst_inv, Prod.snd_inv, star_mul,
    star_soficHyperfinite, star_pauliShiftClass, mul_smul_comm,
    (commute_pauliShiftClass_soficHyperfinite S ω hω x.1⁻¹ x.2⁻¹).eq]

theorem ultratrace_pauliSoficModel (hpos : ∀ n, 0 < Fintype.card (S.model n))
    (x : PauliGroup × G) (hx : x ≠ 1) :
    hyperfiniteUltratrace ω (pauliSoficModel S ω hω x) = 0 := by
  rw [pauliSoficModel]
  by_cases hp : x.1 = 1
  · have hg : x.2 ≠ 1 := fun hg ↦ hx (Prod.ext hp hg)
    rw [hp, pauliShiftClass_one, one_mul, ultratrace_soficHyperfinite S ω hω hpos, if_neg hg]
  · rw [soficHyperfinite]
    exact ultratrace_pauliShiftClass_mul_map S ω hω hp _

end Model

/-- **`L(G) ⊗̄ 𝓡 ↪ R^ω`** (tex 350–355): for a countable sofic group `G` and a free ultrafilter
`ω` on `ℕ`, there is an injective `⋆`-homomorphism from the McDuff factor `L(G) ⊗̄ 𝓡` into the
ultrapower `R^ω` of the hyperfinite II₁ factor. -/
theorem exists_tensorHyperfinite_embedding {G : Type} [Group G] [Countable G] (hG : IsSofic G)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    ∃ Φ : ↥(McDuff.tensorHyperfinite
          (GroupVonNeumann.groupVonNeumannAlgebra G)).toStarSubalgebra →⋆ₐ[ℂ]
        HyperfiniteUltrapower ω, Function.Injective Φ := by
  obtain ⟨S, hpos, -, -⟩ := SoficPermutationTrace.exists_soficApproximation_tendsto_normTrace hG
  haveI : ∀ n, Nonempty (S.model n) := fun n ↦ Fintype.card_pos_iff.mp (hpos n)
  obtain ⟨Φ, hinj, -⟩ := exists_twisted_embedding_of_model
    (TwistedProduct.prodCocycle pauliCocycle (fun _ _ : G ↦ (0 : ZMod 2)))
    (TwistedProduct.isSignCocycle_prodCocycle pauliCocycle_isSignCocycle
      (TwistedProduct.isSignCocycle_zero G)) ω hω
    (pauliSoficModel S ω hω) (pauliSoficModel_one S ω hω) (pauliSoficModel_mul S ω hω)
    (star_pauliSoficModel S ω hω) (fun x hx ↦ ultratrace_pauliSoficModel S ω hω hpos x hx)
  have h1 := TwistedProduct.curryConj_image_twistedTensor pauliCocycle
    (fun _ _ : G ↦ (0 : ZMod 2)) pauliCocycle_isSignCocycle (TwistedProduct.isSignCocycle_zero G)
  rw [TwistedProduct.groupVonNeumannAlgebra_eq_twisted_zero G]
  refine ⟨Φ.comp (SpatialIso.restrictConj TwistedProduct.curryLp h1).toStarAlgHom, ?_⟩
  rw [StarAlgHom.coe_comp]
  exact hinj.comp (EquivLike.injective (SpatialIso.restrictConj TwistedProduct.curryLp h1))

end

end GroupApproximation.SimpleKazhdanSofic.ROmega

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ROmega.exists_tensorHyperfinite_embedding
