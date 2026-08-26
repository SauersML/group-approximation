import GroupApproximation.Analysis.MFAlgebraDimensionNormalization
import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerProjectionZero
import GroupApproximation.Manuscript.OneSidedMFRadical.LiteralMFClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedModelSeparationConverse
import GroupApproximation.Meta.AxiomGuard

/-!
# Literal definition and norm repairs for the current manuscript

This file closes four small discrepancies between the current manuscript and
the declarations used by its sentence census.  It gives the kernel
characterization of the MF radical and the corresponding target-valued form of
the compression criterion, normalizes the separating matrix models at the
identity, states both dimension conventions literally, and takes the square
root of the corrected-corner Kazhdan estimate.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open KazhdanCornerMatrices
open MaximalCStarKazhdanProjection
open PrintedCornerCompression
open UltraproductKazhdanProjection
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## MF targets and the one-sided criterion -/

/-- A subgroup lies in the MF radical exactly when every homomorphism to a
countable MF group kills it.  This is the subgroup-valued, rather than merely
element-valued, form of the literal kernel intersection. -/
def MFTargetKernelCharacterization : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (K : Subgroup G),
    K ≤ manuscriptCoronaMFResidual G ↔
      ∀ (M : Type) (_ : Group M) (_ : Countable M) (f : G →* M),
        IsCDEOperatorMF M → K ≤ f.ker

theorem manuscriptMFTargetKernelCharacterization :
    MFTargetKernelCharacterization := by
  intro G _ _ K
  rw [← literalMFClosure_bot]
  constructor
  · intro hK M _ _ f hM k hk
    exact MonoidHom.mem_ker.mpr
      ((mem_literalMFClosure_iff.mp (hK hk)) M inferInstance inferInstance f hM
        bot_le)
  · intro h k hk
    exact mem_literalMFClosure_iff.mpr fun M _ _ f hM _ ↦
      MonoidHom.mem_ker.mp (h M inferInstance inferInstance f hM hk)

/-- The one-sided compression criterion with its conclusion evaluated in an
arbitrary MF target: every such target homomorphism kills the normal Kazhdan
subgroup, not only its image in a particular matrix corona. -/
def OneSidedCompressionTargetCriterion : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
      ∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
        K ≤ printedDefect L →
          ∀ (M : Type) (_ : Group M) (_ : Countable M) (f : G →* M),
            IsCDEOperatorMF M → K ≤ f.ker

theorem manuscriptOneSidedCompressionTargetCriterion :
    OneSidedCompressionTargetCriterion := by
  intro G _ _ L hL K _ hK hKL M _ _ f hM
  have hrad : K ≤ manuscriptCoronaMFResidual G :=
    (manuscriptOneSidedCompressionCriterion G L hL).1 K hK hKL
  exact (manuscriptMFTargetKernelCharacterization G K).mp hrad
    M inferInstance inferInstance f hM

/-! ## Exactly normalized separating models -/

/-- The model form of group MF with the identity equation included literally.
The lower bound is allowed to depend on the nonidentity element. -/
def NormalizedMFModelSeparation : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    IsCDEOperatorMF G ↔
      ∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ),
        (∀ n, 0 < Fintype.card (X n)) ∧
          (∀ n, V n (1 : G) = 1) ∧
          (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
            ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
              (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
          (∀ g : G, g ≠ 1 → 0 < limsup
            (fun n ↦ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) atTop)

theorem manuscriptNormalizedMFModelSeparation :
    NormalizedMFModelSeparation := by
  intro G _ _
  constructor
  · intro hMF
    obtain ⟨X, V, hX, hmul, hsep⟩ :=
      (manuscriptPrintedMFModelSeparation G).mp hMF
    let A : OpAlmostRepresentation G := {
      model := X
      modelNonempty := hX
      map := V
      asymptoticallyMultiplicative := hmul }
    refine ⟨X, normalizedOpMap A, hX, normalizedOpMap_one A, ?_, ?_⟩
    · exact normalizedOpMap_multiplicative_vanishing A
    · intro g hg
      simpa [normalizedOpMap_of_ne_one A _ hg] using hsep g hg
  · rintro ⟨X, V, hX, _hone, hmul, hsep⟩
    exact isCDEOperatorMF_of_limsup_separating_unitary_models
      G X V hX hmul hsep

/-! ## Arbitrary positive dimension sequences -/

/-- The group definition is unchanged if the positive natural matrix sizes
are arbitrary rather than strictly increasing.  Both sides are displayed
literally, so the statement does not hide the dimension convention in a
renamed predicate. -/
def ArbitraryPositiveDimensionGroupMFDefinition : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    IsCDEOperatorMF G ↔
      ∃ d : ℕ → ℕ, ∃ hd : ∀ n, 0 < d n,
        letI : ∀ n, Nonempty (naturalFiniteModel (d n)) := fun n ↦
          Fintype.card_pos_iff.mp (by simpa using hd n)
        ∃ rho : G →* unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))), Function.Injective rho

theorem manuscriptArbitraryPositiveDimensionGroupMFDefinition :
    ArbitraryPositiveDimensionGroupMFDefinition := by
  intro G _ _
  constructor
  · rintro ⟨d, hd, _hmono, rho, hrho⟩
    exact ⟨d, hd, rho, hrho⟩
  · rintro ⟨d, hd, rho, hrho⟩
    let X : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n)
    letI : ∀ n, Nonempty (X n) := fun n ↦
      Fintype.card_pos_iff.mp (by simpa [X] using hd n)
    apply (isCDEOperatorMF_iff_isOperatorMF G).mpr
    exact ⟨X, (by simpa [X] using hd),
      (normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp rho,
      (normMatrixCoronaUnitaryEquiv X).symm.injective.comp hrho⟩

/-- The algebra definition is likewise unchanged if the positive finite
matrix models are arbitrary rather than strictly increasing. -/
def ArbitraryPositiveDimensionAlgebraMFDefinition : Prop :=
  ∀ (A : Type) [NonUnitalCStarAlgebra A],
    IsMFAlgebra A ↔
      TopologicalSpace.SeparableSpace A ∧
        ∃ X : ℕ → FiniteModel, ∃ hne : ∀ n, Nonempty (X n),
          letI : ∀ n, Nonempty (X n) := hne
          (∀ n, 0 < Fintype.card (X n)) ∧
            ∃ e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n),
              Function.Injective e

theorem manuscriptArbitraryPositiveDimensionAlgebraMFDefinition :
    ArbitraryPositiveDimensionAlgebraMFDefinition := by
  intro A _
  simpa [MFAlgebraDimension.IsUnrestrictedMFAlgebra,
    MFAlgebraDimension.HasUnrestrictedMFEmbedding] using
      MFAlgebraDimension.isMFAlgebra_iff A

/-! ## The unsquared corrected-corner lower bound -/

/-- The corona-class construction with the exact identity normalization kept
in its existential output.  `CornerCoronaClass` deliberately forgot these
three equations even though `manuscriptCentralCoronaCorner` constructs them;
this formulation retains them for the literal norm estimate below. -/
def NormalizedCornerCoronaClass : Prop :=
  ∀ (G : Type) [Group G] [Countable G]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (q : NormMatrixCStarCorona (fun n ↦ X n)),
    star q = q → q * q = q → q ≠ 0 →
    (∀ g : G, ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) * q =
      q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n))) →
    ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (Q : BoundedMatrixSequence (fun n ↦ X n))
      (D : PrintedCornerData G (fun k ↦ X (φ k))),
      (∀ n, IsOrthogonalProjectionMatrix
        ((Q : ∀ n, Matrix (X n) (X n) ℂ) n)) ∧
      normMatrixCStarCoronaMk (fun n ↦ X n) Q = q ∧
      (∀ k, D.q k = (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k)) ∧
      (∀ k, D.q k ≠ 0) ∧
      (∀ k, 0 < Fintype.card (D.cornerModel k)) ∧
      (∀ k g, HEq (D.cornerRepresentation.map k g) (D.cornerMap k g)) ∧
      (∀ k, D.V k (1 : G) = 1) ∧
      (∀ k, D.cornerMap k (1 : G) = 1) ∧
      (∀ k, D.cornerRepresentation.map k (1 : G) = 1) ∧
      (∀ g : G,
        normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ambientCornerSeq D g) =
          coronaRestrict X φ hφ
            (q * ((rho g : unitary
              (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n))))

theorem manuscriptNormalizedCornerCoronaClass :
    NormalizedCornerCoronaClass := by
  intro G _ _ X _ rho q hqstar hqid hqne hcentral
  obtain ⟨Q, φ, D, hφmono, hQproj, hQmk, hDq, hDV, hVone, hcard,
      hHEq, hmapone, hrepone, hpair⟩ :=
    manuscriptCentralCoronaCorner G X rho q hqstar hqid hqne hcentral
  refine ⟨φ, hφmono, Q, D, hQproj, hQmk, hDq, D.q_ne_zero, hcard, hHEq,
    hVone, hmapone, hrepone, ?_⟩
  intro g
  obtain ⟨hclass, hcorr⟩ := hpair g
  set Wg : BoundedMatrixSequence (fun n ↦ X n) :=
    Q * unitarySequenceBounded X (CollapseUnitaryLift.liftFam X rho g) * Q
    with hWg
  have hW : ∀ k, restrictSeq X φ Wg k =
      D.q k * (D.V k g : Matrix (X (φ k)) (X (φ k)) ℂ) * D.q k := by
    intro k
    rw [hWg, hDq k, hDV k g]
    ext i j
    rfl
  have hbound : ∀ k, ‖((ambientCornerSeq D g :
        BoundedMatrixSequence (fun k ↦ X (φ k))) - restrictSeq X φ Wg) k‖
      ≤ ‖(D.cornerMap k g : Matrix (D.cornerModel k)
          (D.cornerModel k) ℂ) - D.compress k g‖ := by
    intro k
    rw [lp.coeFn_sub, Pi.sub_apply, hW k]
    exact norm_ambientCornerMap_sub_compress_le D k g
  have hnull : IsNullMatrixSequence (fun k ↦ X (φ k)) cofinite
      ((ambientCornerSeq D g : BoundedMatrixSequence (fun k ↦ X (φ k))) -
        restrictSeq X φ Wg) := by
    rw [IsNullMatrixSequence, Nat.cofinite_eq_atTop]
    exact squeeze_zero' (Eventually.of_forall fun k ↦ norm_nonneg _)
      (Eventually.of_forall hbound) hcorr
  calc
    normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ambientCornerSeq D g) =
        normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (restrictSeq X φ Wg) := by
      exact (filterMatrixCStarCoronaMk_eq_iff (fun k ↦ X (φ k)) cofinite
        (ambientCornerSeq D g) (restrictSeq X φ Wg)).mpr hnull
    _ = coronaRestrict X φ hφmono
          (normMatrixCStarCoronaMk (fun n ↦ X n) Wg) :=
      (coronaRestrict_mk X φ hφmono Wg).symm
    _ = coronaRestrict X φ hφmono
          (q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))) := by rw [hclass]

/-- The normal-Kazhdan construction with exact normalization retained. -/
theorem exists_normalizedCorrectedCornerProvenanceData
    {G : Type} [Group G] [Countable G]
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (K : Subgroup G) [K.Normal]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (KD : KazhdanData K) (k : K)
    (hk : ((rho (k : G) : unitary
      (NormMatrixCStarCorona (fun n ↦ X n))) :
      NormMatrixCStarCorona (fun n ↦ X n)) ≠ 1) :
    ∃ P : CorrectedCornerProvenanceData G X K,
      (∀ n, P.corner.V n (1 : G) = 1) ∧
      (∀ n, P.corner.cornerMap n (1 : G) = 1) ∧
      (∀ n, P.corner.cornerRepresentation.map n (1 : G) = 1) := by
  let C : KazhdanCompressionRep K G
      (NormMatrixCStarCorona (fun n ↦ X n)) :=
    normalSubgroupKazhdanCompressionData rho K KD
  let p : NormMatrixCStarCorona (fun n ↦ X n) := C.proj
  let q : NormMatrixCStarCorona (fun n ↦ X n) := 1 - p
  have hpstar : star p = p := C.kt_08_isSelfAdjoint_proj.star_eq
  have hpid : p * p = p := C.kt_08_proj_mul_proj
  have hqstar : star q = q := by
    change star (1 - p) = 1 - p
    rw [star_sub, star_one, hpstar]
  have hqid : q * q = q := by
    change (1 - p) * (1 - p) = 1 - p
    rw [sub_mul, one_mul, mul_sub, mul_one, hpid, sub_self, sub_zero]
  have hCk : ((C.pi (C.iota k) : unitary
      (NormMatrixCStarCorona (fun n ↦ X n))) :
      NormMatrixCStarCorona (fun n ↦ X n)) ≠ 1 := hk
  have hqne : q ≠ 0 := NormalKazhdanUltraproduct.nk_06_q_ne_zero C hCk
  have hcentral : ∀ g : G,
      ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * q =
        q * ((rho g : unitary
          (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) := by
    intro g
    have hg : ∀ gamma : K, ∃ delta : K,
        g * C.iota gamma * g⁻¹ = C.iota delta := by
      intro gamma
      exact ⟨⟨g * (gamma : G) * g⁻¹,
        (inferInstance : K.Normal).conj_mem (gamma : G) gamma.property g⟩, rfl⟩
    exact NormalKazhdanUltraproduct.nk_07_commute_q C g hg
  obtain ⟨phi, hphi, Q, D, hQproj, hQclass, hDq, _hDne, _hcard,
      _hmap, hVone, hmapone, hrepone, hclass⟩ :=
    manuscriptNormalizedCornerCoronaClass G X rho q hqstar hqid hqne hcentral
  let P : CorrectedCornerProvenanceData G X K := {
    rho := rho
    kazhdan := KD
    p := p
    q := q
    p_eq := rfl
    q_eq := rfl
    Q := Q
    phi := phi
    phi_strictMono := hphi
    corner := D
    Q_projection := hQproj
    Q_class := hQclass
    corner_q := hDq
    cornerClass := hclass }
  exact ⟨P, hVone, hmapone, hrepone⟩

/-- Taking square roots converts the squared normalized Hilbert--Schmidt
estimate into the literal norm estimate, with the same coordinate identity.
The identity is written as `cornerMap n 1`, and the equality making it the
matrix identity is retained explicitly. -/
def UnsquaredCorrectedCornerKazhdanDetection : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (K : Subgroup G) (_hnormal : K.Normal)
    (_hT : HasKazhdanPropertyT.{0, 0} K)
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n))) (k : K),
    ((rho (k : G) : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) ≠ 1 →
      ∃ P : CorrectedCornerProvenanceData G X K,
        (∀ n, P.corner.cornerMap n (1 : G) = 1) ∧
        ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ cofinite →
          ∃ k0 : K, (k0 : G) ∈ K ∧ k0 ∈ P.kazhdan.S ∧
            0 < P.kazhdan.kappa ^ 2 / (2 * P.kazhdan.S.card) ∧
            (∃ psi : ℕ → ℕ, StrictMono psi ∧ ∀ n,
              Real.sqrt (P.kazhdan.kappa ^ 2 /
                  (2 * P.kazhdan.S.card)) ≤
                hsNorm (P.corner.cornerModel (psi n))
                  ((P.corner.cornerMap (psi n) (k0 : G) :
                    Matrix (P.corner.cornerModel (psi n))
                      (P.corner.cornerModel (psi n)) ℂ) -
                    P.corner.cornerMap (psi n) (1 : G))) ∧
            (k0 : G) ∉ opToHSShadowResidual G

/-! The endpoint proof follows after the normalized provenance constructor
below; it is kept in this file so the square-root statement cannot silently
fall back to the squared estimate. -/

theorem manuscriptUnsquaredCorrectedCornerKazhdanDetection :
    UnsquaredCorrectedCornerKazhdanDetection := by
  intro G _ _ X _ K hnormal hT rho k hk
  letI := hnormal
  obtain ⟨KD⟩ := exists_kazhdanData _ hT
  obtain ⟨P, _hVone, hmapone, _hrepone⟩ :=
    exists_normalizedCorrectedCornerProvenanceData K rho KD k hk
  have hzero := correctedCornerProvenance_kazhdanProjectionZero K P
  refine ⟨P, hmapone, fun ω hω ↦ ?_⟩
  obtain ⟨k0, hk0, hpos, ⟨psi, hpsi, hbound⟩, hout⟩ :=
    correctedCornerProvenance_printedDetection K P ω hω (hzero ω hω)
  refine ⟨k0, k0.2, hk0, hpos, ⟨psi, hpsi, ?_⟩, hout⟩
  intro n
  simpa [hsNorm, hmapone (psi n)] using Real.sqrt_le_sqrt (hbound n)

#audit_closed_axioms manuscriptMFTargetKernelCharacterization
#audit_closed_axioms manuscriptOneSidedCompressionTargetCriterion
#audit_closed_axioms manuscriptNormalizedMFModelSeparation
#audit_closed_axioms manuscriptArbitraryPositiveDimensionGroupMFDefinition
#audit_closed_axioms manuscriptArbitraryPositiveDimensionAlgebraMFDefinition
#audit_closed_axioms manuscriptNormalizedCornerCoronaClass
#audit_closed_axioms manuscriptUnsquaredCorrectedCornerKazhdanDetection

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
