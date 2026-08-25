import GroupApproximation.Analysis.CoronaProjectionOrder
import GroupApproximation.Analysis.MaximalCStarKazhdanProjection
import GroupApproximation.Analysis.PolarLiftingGeneralCStar
import GroupApproximation.Analysis.UnitaryAverageFixedVector
import GroupApproximation.Criterion.FiniteDimensionalKill
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedSectorProof
import GroupApproximation.Sofic.MarkedCompressionSequentialKill
import GroupApproximation.Sofic.UltraproductKazhdanTransport

/-!
# Literal closure of the printed transport proof sentences

This file states the intermediate sentences of the printed proofs themselves:
the displayed commutant computation, the Gram defect of an arbitrary lift, the
complementary-corner isometry, the maximal-group-C-star extension and its
Kazhdan projection, the faithful-representation passage, the ordering of the
nonfaithful action, and the standalone three-factor microstate defect.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix MaximalCStarKazhdanProjection
open AbstractSpectralGap CStarSpectralProjection
open KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v w

/-! ## The displayed finite-dimensional commutant computation -/

/-- **Sentence 100, verbatim algebraic chain.** -/
theorem manuscriptSentence100_commutantComputation
    {k : Type u} {V : Type v} {H : Type w}
    [Field k] [AddCommGroup V] [Module k V] [Group H]
    (pi : H →* Module.End k V) (Gamma : Set H) (t : H)
    (hcomp : ∀ h ∈ Gamma, t * h * t⁻¹ ∈ Gamma)
    (x : Module.End k V) (hx : x ∈ repCommutant pi Gamma)
    (h : H) (hh : h ∈ Gamma) :
    let h' := t * h * t⁻¹
    pi h * (pi t⁻¹ * x * pi t) =
        pi t⁻¹ * pi h' * x * pi t ∧
      pi t⁻¹ * pi h' * x * pi t =
        pi t⁻¹ * x * pi h' * pi t ∧
      pi t⁻¹ * x * pi h' * pi t =
        (pi t⁻¹ * x * pi t) * pi h := by
  dsimp only
  have hleft : pi t⁻¹ * pi t = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have himage : pi (t * h * t⁻¹) = pi t * pi h * pi t⁻¹ := by
    rw [map_mul, map_mul]
  have hprefix : pi t⁻¹ * pi (t * h * t⁻¹) = pi h * pi t⁻¹ := by
    rw [himage]
    calc
      pi t⁻¹ * (pi t * pi h * pi t⁻¹) =
          (pi t⁻¹ * pi t) * pi h * pi t⁻¹ := by noncomm_ring
      _ = pi h * pi t⁻¹ := by rw [hleft, one_mul]
  have hsuffix : pi (t * h * t⁻¹) * pi t = pi t * pi h := by
    rw [himage]
    calc
      (pi t * pi h * pi t⁻¹) * pi t =
          pi t * pi h * (pi t⁻¹ * pi t) := by noncomm_ring
      _ = pi t * pi h := by rw [hleft, mul_one]
  have hcomm : pi (t * h * t⁻¹) * x = x * pi (t * h * t⁻¹) :=
    hx _ (hcomp h hh)
  constructor
  · calc
      pi h * (pi t⁻¹ * x * pi t) = (pi h * pi t⁻¹) * x * pi t := by
        noncomm_ring
      _ = (pi t⁻¹ * pi (t * h * t⁻¹)) * x * pi t := by rw [← hprefix]
      _ = pi t⁻¹ * pi (t * h * t⁻¹) * x * pi t := rfl
  constructor
  · simpa only [mul_assoc] using congrArg (fun y ↦ pi t⁻¹ * y * pi t) hcomm
  · calc
      pi t⁻¹ * x * pi (t * h * t⁻¹) * pi t =
          (pi t⁻¹ * x) * (pi (t * h * t⁻¹) * pi t) := by noncomm_ring
      _ = (pi t⁻¹ * x) * (pi t * pi h) := by rw [hsuffix]
      _ = (pi t⁻¹ * x * pi t) * pi h := by noncomm_ring

/-- **Sentence 101.**  Inverse conjugation sends the commutant into itself. -/
theorem manuscriptSentence101_inverseConjugation_maps_commutant
    {k : Type u} {V : Type v} {H : Type w}
    [Field k] [AddCommGroup V] [Module k V] [Group H]
    (pi : H →* Module.End k V) (Gamma : Set H) (t : H)
    (hcomp : ∀ h ∈ Gamma, t * h * t⁻¹ ∈ Gamma) :
    ∀ x ∈ repCommutant pi Gamma,
      pi t⁻¹ * x * pi t ∈ repCommutant pi Gamma := by
  intro x hx h hh
  exact (manuscriptSentence100_commutantComputation
    pi Gamma t hcomp x hx h hh).1.trans
      ((manuscriptSentence100_commutantComputation
        pi Gamma t hcomp x hx h hh).2.1.trans
        (manuscriptSentence100_commutantComputation
          pi Gamma t hcomp x hx h hh).2.2)

/-! ## The coordinate defect of an arbitrary bounded lift -/

/-- **Sentence 116.**  If `v*v=1` in a norm matrix corona and `x` is any
bounded lift of `v`, then `x_n*x_n-1` tends to zero in operator norm. -/
theorem manuscriptSentence116_anyLift_gramDefect_tendsto
    (X : ℕ → Type u) [∀ n, Fintype (X n)]
    [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]
    (v : NormMatrixCStarCorona X)
    (hv : star v * v = 1)
    (x : BoundedMatrixSequence X)
    (hx : normMatrixCStarCoronaMk X x = v) :
    Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) cofinite (nhds 0) := by
  apply (normMatrixCStarCoronaMk_eq_zero_iff X (star x * x - 1)).mp
  rw [map_sub, map_mul, map_one, ← normMatrixCStarCorona_star_mk, hx, hv,
    sub_self]

/-! ## The complementary-corner isometry -/

/-- **Sentence 122, the printed `w + (1-q)` computation.** -/
theorem manuscriptSentence122_cornerExtension_isometry
    {A : Type u} [CStarAlgebra A] {p q w : A}
    (hq : IsStarProjection q)
    (hqp : q * p = p) (hwstarw : star w * w = q)
    (hwwstar : w * star w = p) :
    star (w + (1 - q)) * (w + (1 - q)) = 1 := by
  have hcorner : q * w * q = w :=
    cstar_corner_eq_of_isometryPair hq hqp hwstarw hwwstar
  have hqw : q * w = w := by
    calc q * w = q * (q * w * q) := by rw [hcorner]
      _ = (q * q) * w * q := by noncomm_ring
      _ = q * w * q := by rw [hq.isIdempotentElem.eq]
      _ = w := hcorner
  have hwq : w * q = w := by
    calc w * q = (q * w * q) * q := by rw [hcorner]
      _ = q * w * (q * q) := by noncomm_ring
      _ = q * w * q := by rw [hq.isIdempotentElem.eq]
      _ = w := hcorner
  have hstarwq : star w * q = star w := by
    have h := congrArg star hqw
    rwa [star_mul, hq.isSelfAdjoint.star_eq] at h
  have hqstarw : q * star w = star w := by
    have h := congrArg star hwq
    rwa [star_mul, hq.isSelfAdjoint.star_eq] at h
  have hstar : star (w + (1 - q)) = star w + (1 - q) := by
    rw [star_add, star_sub, star_one, hq.isSelfAdjoint.star_eq]
  have hcross₁ : star w * (1 - q) = 0 := by
    rw [mul_sub, mul_one, hstarwq, sub_self]
  have hcross₂ : (1 - q) * w = 0 := by
    rw [sub_mul, one_mul, hqw, sub_self]
  have hcomplement : (1 - q) * (1 - q) = 1 - q := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hq.isIdempotentElem.eq,
      sub_self, sub_zero]
  rw [hstar]
  calc
    (star w + (1 - q)) * (w + (1 - q)) =
        star w * w + star w * (1 - q) + (1 - q) * w +
          (1 - q) * (1 - q) := by noncomm_ring
    _ = q + 0 + 0 + (1 - q) := by
      rw [hwstarw, hcross₁, hcross₂, hcomplement]
    _ = 1 := by abel

/-! ## The maximal-C-star Kazhdan projection and its represented range -/

/-- **Sentences 124, 138 and 139.**  One Kazhdan projection is constructed in
`C*_max(L)`; each target representation extends uniquely, and `P` is literally
the image of that projection. -/
theorem manuscriptSentences124_138_139_maximalCStarImage :
    MaximalCStarKazhdanProjectionOrder.{u, v} :=
  manuscriptMaximalCStarKazhdanProjectionOrder

/-- **Sentence 124, separately named:** the Kazhdan projection is a single
element of the maximal group C-star algebra and every target `P` is its image. -/
theorem manuscriptSentence124_maximalCStarKazhdanProjection :
    MaximalCStarKazhdanProjectionOrder.{u, v} :=
  manuscriptMaximalCStarKazhdanProjectionOrder

/-- **Sentence 139, separately named:** `P` in the target is the image of the
maximal-C-star Kazhdan projection, not a newly substituted projection. -/
theorem manuscriptSentence139_imageOfMaximalKazhdanProjection :
    MaximalCStarKazhdanProjectionOrder.{u, v} :=
  manuscriptMaximalCStarKazhdanProjectionOrder

/-- **Sentence 138, separately named.** -/
theorem manuscriptSentence138_maximalCStarExtension
    (L : Type u) [Group L] (B : Type v) [CStarAlgebra B]
    (rho : L →* unitary B) :
    ∃! f : MaximalGroupCStar L →⋆ₐ[ℂ] B,
      ∀ l : L, f (maximalGroupCStarGenerator L l) = (rho l : B) :=
  maximalGroupCStar_existsUnique_lift_allUniverses L rho

/-- **Sentence 126.**  Under a faithful representation, the represented image
of the maximal-C-star Kazhdan projection is the orthogonal star projection
onto exactly the vectors fixed by `rho(L)`. -/
theorem manuscriptSentence126_representedKazhdanProjection_range
    {L : Type u} [Group L] (K : KazhdanData L)
    {B : Type (u + 1)} [CStarAlgebra B]
    {E : Type (u + 1)} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (rho : L →* unitary B)
    (f : MaximalGroupCStar L →⋆ₐ[ℂ] B)
    (hf : ∀ l : L, f (maximalGroupCStarGenerator L l) = (rho l : B))
    (faithfulRep : B →⋆ₐ[ℂ] (E →L[ℂ] E))
    (_hfaithful : Function.Injective faithfulRep) :
    IsStarProjection (faithfulRep (f K.projection)) ∧
      ∀ x : E,
        faithfulRep (f K.projection) x = x ↔
          ∀ l : L, faithfulRep (rho l : B) x = x := by
  let rhoE : L →* unitary (E →L[ℂ] E) :=
    (unitaryMap faithfulRep).comp rho
  let fE : MaximalGroupCStar L →⋆ₐ[ℂ] (E →L[ℂ] E) := faithfulRep.comp f
  have hfE : ∀ l : L,
      fE (maximalGroupCStarGenerator L l) = (rhoE l : E →L[ℂ] E) := by
    intro l
    simp [fE, rhoE, hf l, unitaryMap_coe]
  have hgap : ∀ mu ∈ spectrum ℝ (unitaryAverage rhoE K.S),
      mu ≤ K.rate ∨ mu = 1 := by
    intro mu hmu
    by_cases hmu1 : mu = 1
    · exact Or.inr hmu1
    · left
      have hmuC : (mu : ℂ) ∈ spectrum ℂ (unitaryAverage rhoE K.S) := by
        have h := spectrum.algebraMap_mem ℂ hmu
        rwa [show (algebraMap ℝ ℂ) mu = (mu : ℂ) by simp] at h
      exact UltraproductKazhdanProjection.unitaryAverage_spectrum_le_manuscript
        rhoE K.kazhdan K.S
        Finset.Subset.rfl K.one_mem K.symm hmuC hmu1
  have himage : faithfulRep (f K.projection) =
      spectralProjection (unitaryAverage rhoE K.S) K.rate := by
    change fE K.projection = spectralProjection (unitaryAverage rhoE K.S) K.rate
    exact MaximalCStarKazhdanProjection.image_eq_spectralProjection
      K rhoE fE hfE hgap
  constructor
  · change IsStarProjection (fE K.projection)
    exact MaximalCStarKazhdanProjection.isStarProjection_image K fE
  · intro x
    rw [himage]
    have hset := UnitaryAverageFixedVector.spectralProjection_apply_eq_self_iff
      rhoE ⟨1, K.one_mem⟩ K.symm K.rate_lt_one hgap x
    constructor
    · intro hx l
      have hxS : ∀ g ∈ (K.S : Set L),
          ((rhoE g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x := by
        intro g hg
        exact hset.mp hx g (Finset.mem_coe.1 hg)
      have hl : l ∈ Subgroup.closure (K.S : Set L) := by
        rw [K.generates]
        trivial
      simpa [rhoE, unitaryMap_coe] using
        UnitaryAverageFixedVector.apply_eq_self_of_mem_closure rhoE hxS hl
    · intro hx
      apply hset.mpr
      intro g _
      simpa [rhoE, unitaryMap_coe] using hx g

/-- **Sentence 129.**  A faithful star representation reflects projection
order from `B(H)` to the source algebra. -/
theorem manuscriptSentence129_faithfulRepresentation_reflectsProjectionOrder
    {B : Type u} [CStarAlgebra B] {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (pi : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (hpi : Function.Injective pi)
    {p q : B} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hle : pi q ≤ pi p) : q * p = q :=
  le_of_le_in_faithful_rep pi hpi hp hq hle

/-- **Sentence 141.**  The projection identity is proved inside the algebra
before any possibly nonfaithful representation is used. -/
theorem manuscriptSentence141_identity_before_nonfaithfulRepresentation
    {A : Type u} [CStarAlgebra A] [IsDedekindFiniteMonoid A]
    {p unitary : A} (hp : IsStarProjection p)
    (hu : star unitary * unitary = 1)
    (habsorb : (unitary * p * star unitary) * p = p) :
    unitary * p * star unitary = p ∧
      ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
        [CompleteSpace E] (representation : A →⋆ₐ[ℂ] (E →L[ℂ] E)),
        representation (unitary * p * star unitary) = representation p := by
  have hinside : unitary * p * star unitary = p :=
    kt_10_finiteness_reverses_conjugate
      hp.isSelfAdjoint.star_eq hp.isIdempotentElem.eq hu habsorb
  exact ⟨hinside, fun representation ↦
    congrArg (fun a ↦ representation a) hinside⟩

/-! ## The standalone triple-conjugation defect -/

/-- **Sentence 150, exactly the displayed operator-norm limit.** -/
theorem manuscriptSentence150_tripleConjugationDefect
    {G : Type u} [Group G] (V : OpAlmostRepresentation G) (u c : G) :
    OpNormVanishing V (fun n ↦
      (V.map n u : Matrix (V.model n) (V.model n) ℂ) * V.map n c *
          (V.map n u : Matrix (V.model n) (V.model n) ℂ)ᴴ -
        V.map n (u * c * u⁻¹)) :=
  KazhdanCompressorCorner.conj_matrix_defect_vanishing V u c

/-- Auditable maximal-C-star surface shared by the literal sentence theorems. -/
theorem manuscriptSentenceTransportClosure :
    MaximalCStarKazhdanProjectionOrder.{u, v} :=
  manuscriptSentences124_138_139_maximalCStarImage

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
