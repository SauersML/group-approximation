import GroupApproximation.Sofic.FiniteNormalAverageCorner
import GroupApproximation.Sofic.MarkedCompressionRootCapture
import GroupApproximation.Sofic.MarkedCompressionSequentialKill
import Mathlib.Order.Filter.Finite

/-!
# Finite normal subgroups in a Kazhdan-compression defect

This file isolates the stronger, Clifford-free form of the marked-compression
obstruction.  Its group-theoretic input consists only of

* a property-`(T)` group `Γ` mapped into an ambient group `E`;
* an element `t` with `t · ι(Γ) · t⁻¹ ⊆ ι(Γ)`;
* an element `c` centralizing `ι(Γ)`.

Writing `d = t c t⁻¹`, the compression-defect subgroup is the normal closure
of the commutators `[d, ι(γ)]`.  The intended analytic theorem says that every
finite normal subgroup contained in this defect subgroup is invisible to all
operator-norm matrix ultraproducts.

The previously formalized central-involution theorem is the special case in
which one distinguished element of the defect subgroup is central of order
two.  The finite-normal theorem averages over the finite normal subgroup,
cuts to the complementary central corner, and runs the marker-parametric
Kazhdan-compressor argument there.  The resulting universal kernel theorem is
`KazhdanCompressionCore.finiteNormal_le_normMFResidual`.
-/

namespace GroupApproximation

open Filter KazhdanCornerMatrices KazhdanCompressorCorner
open scoped commutatorElement Matrix.Norms.L2Operator

variable {Γ E : Type} [Group Γ] [Group E]

namespace KazhdanCompressionCore

/-- Hilbert--Schmidt triviality of every pointwise compression defect in an
operator-norm almost representation. -/
def CompressionDefectsHSTrivial (C : KazhdanCompressionCore Γ E)
    (B : OpAlmostRepresentation E) : Prop :=
  ∀ γ : Γ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
    hsDistSq (B.model n)
      (B.map n ⁅C.transported, C.iota γ⁆) (B.map n 1) ≤ epsilon

/-- **Marker-free Kazhdan compression collapse.**  Root capture applies
directly to the compression core; no distinguished word is introduced. -/
theorem compressionDefects_hsTrivial
    (C : KazhdanCompressionCore Γ E) (B : OpAlmostRepresentation E) :
    CompressionDefectsHSTrivial C B := by
  intro gamma epsilon hepsilon
  simpa [transported] using
    KazhdanCompressorCorner.compressionDefect_hsDistSq_vanishing
      B C gamma epsilon hepsilon

/-- Every operator-norm almost representation canonically gives an
asymptotic unitary representation for the normalized Hilbert--Schmidt
metric. -/
noncomputable def toAsymptoticUnitaryRepresentation
    (B : OpAlmostRepresentation E) : AsymptoticUnitaryRepresentation E where
  model := B.model
  modelNonempty := B.modelNonempty
  map := B.map
  asymptoticallyMultiplicative := by
    intro g h epsilon hepsilon
    obtain ⟨N, hN⟩ := B.asymptoticallyMultiplicative g h
      (Real.sqrt epsilon) (Real.sqrt_pos.2 hepsilon)
    refine ⟨N, fun n hn ↦ ?_⟩
    let R : Matrix (B.model n) (B.model n) ℂ :=
      (B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h
    have hop : ‖R‖ ≤ Real.sqrt epsilon := hN n hn
    calc
      hsDistSq (B.model n) (B.map n (g * h))
          ((B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h) ≤
        ‖R‖ ^ 2 := hsDistSq_le_sq_l2_opNorm (B.model n) _ _
      _ ≤ (Real.sqrt epsilon) ^ 2 := by
        nlinarith [norm_nonneg R, Real.sqrt_nonneg epsilon]
      _ = epsilon := Real.sq_sqrt hepsilon.le

end KazhdanCompressionCore

namespace MarkedCompressionInclusionData

/-- The original marked commutator already lies in the broader
compression-defect normal subgroup.  Indeed, after quotienting by all
`[d, ι(γ)]`, the transported root `d` commutes with `ι(a)`, so its commutator
with the `ι(a)`-conjugate of `d` vanishes. -/
theorem word_mem_compressionDefectNormal
    (D : MarkedCompressionInclusionData Γ E) :
    D.word ∈ D.toKazhdanCompressionCore.defectNormal := by
  let C := D.toKazhdanCompressionCore
  let N := C.defectNormal
  let q : E →* E ⧸ N := QuotientGroup.mk' N
  have hdefect : ⁅C.transported, C.iota D.a⁆ ∈ N :=
    C.defect_mem_defectNormal D.a
  have hdefectQ : ⁅q C.transported, q (C.iota D.a)⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).2 hdefect
  have hcomm : Commute (q C.transported) (q (C.iota D.a)) :=
    commutatorElement_eq_one_iff_commute.mp hdefectQ
  have hconj :
      q (C.iota D.a) * q C.transported * (q (C.iota D.a))⁻¹ =
        q C.transported := by
    calc
      q (C.iota D.a) * q C.transported * (q (C.iota D.a))⁻¹ =
          q C.transported * q (C.iota D.a) * (q (C.iota D.a))⁻¹ := by
            rw [← hcomm.eq]
      _ = q C.transported := by group
  apply (QuotientGroup.eq_one_iff D.word).mp
  change q D.word = 1
  rw [MarkedCompressionInclusionData.word, map_markedCompressionWord]
  change ⁅q C.transported,
    q (C.iota D.a) * q C.transported * (q (C.iota D.a))⁻¹⁆ = 1
  rw [hconj, commutatorElement_self]

end MarkedCompressionInclusionData

namespace KazhdanCompressionCore

/-- **Finite-normal Kazhdan-compression obstruction (analytic core).**

If a finite normal subgroup is contained in the normal closure of the
compression defects, every operator-norm matrix-ultraproduct homomorphism
kills it.

The proof has two reusable components:

1. parameterize `commutatorMatrix_hsDistSq_vanishing` by an arbitrary
   `γ : Γ`, showing that every `[d, ι(γ)]` becomes Hilbert--Schmidt trivial in
   the adjoint Kazhdan corner, and propagate this through the normal closure;
2. for a homomorphism that is nontrivial on the finite normal subgroup `F`,
   form `p_F = |F|⁻¹ ∑_{f∈F} ρ(f)`, cut to `q_F = 1 - p_F`, and extract a
   sequential matrix-corner model.  On that corner the same finite average is
   exactly zero, whereas (1) makes every summand Hilbert--Schmidt converge to
   one, a contradiction.

Everything after this lemma is a purely formal residual argument. -/
theorem finiteNormal_le_normMFResidual
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ C.defectNormal) :
    F ≤ normMFResidual E := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  intro f hf I U X rho
  by_contra hsurvive
  have hnontrivial : ∃ x : F, rho x ≠ 1 := by
    refine ⟨⟨f, hf⟩, ?_⟩
    simpa using hsurvive
  obtain ⟨B, hsum⟩ :=
    FiniteNormalAverageCorner.exists_corner_with_finite_sum_vanishing
      F U X rho hnontrivial
  let U₀ : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have hcof : ((U₀ : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
    Ultrafilter.of_le Filter.cofinite
  let S := toAsymptoticUnitaryRepresentation B
  let rhoHS : E →* UniversalHyperlinear U₀ S.model S.modelNonempty :=
    S.toUltraproductHom hcof
  have hdefect : ∀ gamma : Γ,
      rhoHS ⁅C.transported, C.iota gamma⁆ = 1 := by
    intro gamma
    have hcollapse := compressionDefects_hsTrivial C B gamma
    have hnull :
        (fun n ↦ S.map n ⁅C.transported, C.iota gamma⁆)⁻¹ *
            (fun n ↦ S.map n 1) ∈
          nullUnitarySubgroup U₀ S.model S.modelNonempty := by
      intro epsilon hepsilon
      obtain ⟨N, hN⟩ := hcollapse (epsilon / 2) (by linarith)
      refine eventually_of_atTop hcof N (fun n hn ↦ ?_)
      show hsLengthSq (S.model n)
        (((S.map n ⁅C.transported, C.iota gamma⁆)⁻¹ * S.map n 1 :
          Matrix.unitaryGroup (S.model n) ℂ)) < epsilon
      rw [coe_inv_mul,
        hsLengthSq_conjTranspose_mul (S.model n)
          (S.map n ⁅C.transported, C.iota gamma⁆).2
          (S.modelNonempty n),
        KazhdanCompressorCorner.hsDistSq_comm]
      exact lt_of_le_of_lt (hN n hn) (by linarith)
    have heq :
        QuotientGroup.mk
            (fun n ↦ S.map n ⁅C.transported, C.iota gamma⁆) =
          QuotientGroup.mk (fun n ↦ S.map n 1) :=
      QuotientGroup.eq.mpr hnull
    calc
      rhoHS ⁅C.transported, C.iota gamma⁆ =
          QuotientGroup.mk
            (fun n ↦ S.map n ⁅C.transported, C.iota gamma⁆) := rfl
      _ = QuotientGroup.mk (fun n ↦ S.map n 1) := heq
      _ = rhoHS 1 := rfl
      _ = 1 := map_one rhoHS
  have hkillF : ∀ x : F, rhoHS (x : E) = 1 := by
    intro x
    exact C.map_eq_one_of_mem_of_defects_eq_one rhoHS hdefect F hF x
  have hcloseU : ∀ x : F, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n in (U₀ : Filter ℕ),
        hsDistSq (B.model n) (B.map n (x : E)) (B.map n 1) < epsilon := by
    intro x epsilon hepsilon
    have heqRho : rhoHS (x : E) = rhoHS 1 := by
      rw [hkillF x, map_one]
    have heqMk :
        (QuotientGroup.mk (fun n ↦ S.map n (x : E)) :
          UniversalHyperlinear U₀ S.model S.modelNonempty) =
        QuotientGroup.mk (fun n ↦ S.map n 1) := by
      simpa [rhoHS] using heqRho
    have hnull :
        (fun n ↦ S.map n 1)⁻¹ * (fun n ↦ S.map n (x : E)) ∈
          nullUnitarySubgroup U₀ S.model S.modelNonempty :=
      QuotientGroup.eq.mp heqMk.symm
    filter_upwards [hnull epsilon hepsilon] with n hn
    change hsLengthSq (S.model n)
      (((S.map n 1)⁻¹ * S.map n (x : E) :
        Matrix.unitaryGroup (S.model n) ℂ)) < epsilon at hn
    rw [coe_inv_mul,
      hsLengthSq_conjTranspose_mul (S.model n) (S.map n 1).2
        (S.modelNonempty n)] at hn
    exact hn
  let eta : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have heta (n : ℕ) : 0 < eta n := by dsimp [eta]; positivity
  have hall : ∀ n : ℕ, ∀ᶠ i in (U₀ : Filter ℕ),
      n ≤ i ∧ ∀ x : F,
        hsDistSq (B.model i) (B.map i (x : E)) (B.map i 1) < eta n := by
    intro n
    have htail : ∀ᶠ i in (U₀ : Filter ℕ), n ≤ i :=
      eventually_of_atTop hcof n (fun _ hi ↦ hi)
    have hfinite : ∀ᶠ i in (U₀ : Filter ℕ), ∀ x : F,
        hsDistSq (B.model i) (B.map i (x : E)) (B.map i 1) < eta n := by
      have hfinite' : ∀ᶠ i in (U₀ : Filter ℕ),
          ∀ x ∈ (Finset.univ : Finset F),
            hsDistSq (B.model i) (B.map i (x : E))
              (B.map i 1) < eta n := by
        rw [eventually_all_finset]
        intro x _
        exact hcloseU x (eta n) (heta n)
      simpa using hfinite'
    exact htail.and hfinite
  let stage : ℕ → ℕ := fun n ↦ Classical.choose (hall n).exists
  have hstage (n : ℕ) :
      n ≤ stage n ∧ ∀ x : F,
        hsDistSq (B.model (stage n))
          (B.map (stage n) (x : E)) (B.map (stage n) 1) < eta n :=
    Classical.choose_spec (hall n).exists
  let B' := B.reindex stage (fun n ↦ (hstage n).1)
  have hsum' : KazhdanCornerMatrices.OpNormVanishing B' (fun n ↦
      ∑ x : F, (B'.map n (x : E) :
        Matrix (B'.model n) (B'.model n) ℂ)) := by
    have hr := FiniteNormalAverageCorner.OpNormVanishing.reindex
      hsum stage (fun n ↦ (hstage n).1)
    change KazhdanCornerMatrices.OpNormVanishing B' _ at hr
    exact hr.congr (fun _ ↦ rfl)
  have hclose' : ∀ x : F,
      FiniteNormalAverageCorner.HSDistVanishing B' (x : E) 1 := by
    intro x epsilon hepsilon
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / epsilon)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hNen : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hsmall : eta n ≤ epsilon := by
      dsimp [eta]
      have hlt : (1 : ℝ) / epsilon < (n : ℝ) + 1 := by linarith
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hepsilon] at hlt
      linarith
    exact le_trans (le_of_lt ((hstage n).2 x)) hsmall
  exact FiniteNormalAverageCorner.false_of_finite_sum_vanishing_of_hsTrivial
    B' F hsum' hclose'

/-- A nontrivial finite normal subgroup inside the compression defect rules
out weak/operator-norm MF approximation. -/
theorem not_isWeakMF_of_finiteNormal_le_defect
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (F : Subgroup E) [Finite F] [F.Normal] [Nontrivial F]
    (hF : F ≤ C.defectNormal) :
    ¬ IsWeakMF E := by
  obtain ⟨f, hf⟩ := exists_ne (1 : F)
  have hfinv : NormMFInvisible (f : E) :=
    C.finiteNormal_le_normMFResidual F hF f.property
  apply not_isWeakMF_of_normMFInvisible hfinv
  intro h
  apply hf
  apply Subtype.ext
  simpa using h

end KazhdanCompressionCore

namespace MarkedCompressionInclusionData

/-- The finite-normal theorem recovers the marked-word conclusion whenever
the marked word is placed in a finite normal subgroup.  The separate
`word_mem_compressionDefectNormal` theorem supplies the required containment
for the cyclic marked subgroup in the explicit construction. -/
theorem word_normMFInvisible_of_mem_finiteNormal
    [Countable E] (D : MarkedCompressionInclusionData Γ E)
    (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ D.toKazhdanCompressionCore.defectNormal)
    (hword : D.word ∈ F) :
    NormMFInvisible D.word :=
  D.toKazhdanCompressionCore.finiteNormal_le_normMFResidual F hF hword

/-- Endpoint form of the previous compatibility result. -/
theorem not_isWeakMF_of_mem_finiteNormal
    [Countable E] (D : MarkedCompressionInclusionData Γ E)
    (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ D.toKazhdanCompressionCore.defectNormal)
    (hword : D.word ∈ F) (hne : D.word ≠ 1) :
    ¬ IsWeakMF E :=
  not_isWeakMF_of_normMFInvisible
    (D.word_normMFInvisible_of_mem_finiteNormal F hF hword) hne

end MarkedCompressionInclusionData

end GroupApproximation
