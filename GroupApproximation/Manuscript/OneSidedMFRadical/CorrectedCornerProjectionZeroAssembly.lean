import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerProjectionZeroTransport
import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerCoronaEmbedding
import GroupApproximation.Manuscript.OneSidedMFRadical.MaximalCStarTrivialCharacter
import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerProvenanceData
import GroupApproximation.Manuscript.OneSidedMFRadical.RetainedCoronaHom
import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerAmbientKazhdanImage

/-!
# The complementary Kazhdan projection in the corrected corner

This file supplies the compatibility layer deliberately absent from
`PrintedCornerData`: the data constructed by `manuscriptCornerCoronaClass`
comes from `q = 1 - p`, where `p` is the image of the maximal Kazhdan
projection.  The coordinate corner embedding descends to an injective
nonunital star homomorphism of the corresponding omega coronas.  It is this
map, together with uniqueness of the maximal group-C-star lift, that turns
the elementary identity `(1-p) * p * (1-p) = 0` into vanishing of the
Kazhdan projection in the actual polar-corrected corner representation.

The restriction constructor below is essential: the ambient corner maps are
indexed by the ambient group, whereas the Kazhdan datum belongs only to its
normal property-(T) subgroup.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter PrintedCornerCompression
open MaximalCStarKazhdanProjection OmegaCoronaKazhdanProjection
open AbstractSpectralGap

noncomputable section

/-! ## Projection-zero from the retained compression identity -/

/-- The algebraic heart of the assembly.  If the embedded corrected generators
are `(1-p)ρ(k)`, while `p` is the represented Kazhdan projection and absorbs
every `ρ(k)`, then the corrected representation sends the Kazhdan projection
to zero. -/
theorem correctedCornerProjectionZero_of_retainedCompression
    {K : Type} [Group K] {model : ℕ → FiniteModel}
    [∀ n, Nonempty (model n)]
    (D : PrintedCornerData K model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (KD : KazhdanData K)
    (rhoA : K →* unitary
      (FilterMatrixCStarCorona (fun n ↦ model n) (ω : Filter ℕ)))
    (F : MaximalGroupCStar K →⋆ₐ[ℂ]
      FilterMatrixCStarCorona (fun n ↦ model n) (ω : Filter ℕ))
    (hF : ∀ k : K,
      F (maximalGroupCStarGenerator K k) =
        ((rhoA k : unitary
          (FilterMatrixCStarCorona (fun n ↦ model n) (ω : Filter ℕ))) :
          FilterMatrixCStarCorona (fun n ↦ model n) (ω : Filter ℕ)))
    (hcorner : ∀ k : K,
      correctedCornerCoronaEmbedHom D (ω : Filter ℕ)
          (((coronaRep (fun n ↦ D.cornerModel n) ω
            (correctedCornerOmegaRepresentation D ω hω) k :
              unitary (FilterMatrixCStarCorona
                (fun n ↦ D.cornerModel n) (ω : Filter ℕ))) :
            FilterMatrixCStarCorona
              (fun n ↦ D.cornerModel n) (ω : Filter ℕ))) =
        (1 - F KD.projection) *
          ((rhoA k : unitary
            (FilterMatrixCStarCorona (fun n ↦ model n) (ω : Filter ℕ))) :
            FilterMatrixCStarCorona (fun n ↦ model n) (ω : Filter ℕ))) :
    KazhdanProjectionZeroForRepresentation KD
      (coronaRep (fun n ↦ D.cornerModel n) ω
        (correctedCornerOmegaRepresentation D ω hω)) := by
  let C := FilterMatrixCStarCorona
    (fun n ↦ D.cornerModel n) (ω : Filter ℕ)
  let A := FilterMatrixCStarCorona (fun n ↦ model n) (ω : Filter ℕ)
  let rhoC : K →* unitary C :=
    coronaRep (fun n ↦ D.cornerModel n) ω
      (correctedCornerOmegaRepresentation D ω hω)
  let e : C →⋆ₙₐ[ℂ] A :=
    correctedCornerCoronaEmbedHom D (ω : Filter ℕ)
  have heone : e 1 = 1 - F KD.projection := by
    have h := hcorner (1 : K)
    change e (((rhoC 1 : unitary C) : C)) =
      (1 - F KD.projection) * (((rhoA 1 : unitary A) : A)) at h
    simpa using h
  have hfixLeft : ∀ k : K,
      F KD.projection * (((rhoA k : unitary A) : A)) = F KD.projection := by
    intro k
    have hcanon := KD.generator_mul_projection k⁻¹
    have himage := congrArg F hcanon
    rw [map_mul, hF k⁻¹] at himage
    have hstar := congrArg star himage
    have hsa : star (F KD.projection) = F KD.projection :=
      (isSelfAdjoint_image KD F).star_eq
    simpa only [star_mul, hsa, star_unitary_coe rhoA (k⁻¹), inv_inv]
      using hstar
  intro f hf
  let ef : MaximalGroupCStar K →⋆ₙₐ[ℂ] A :=
    e.comp f.toNonUnitalStarAlgHom
  let L : MaximalGroupCStar K →⋆ₐ[ℂ] A :=
    complementUnitizedStarAlgHom ef (maximalGroupCStarTrivialCharacter K)
  have hLgen : ∀ k : K,
      L (maximalGroupCStarGenerator K k) =
        ((rhoA k : unitary A) : A) := by
    intro k
    change e (f (maximalGroupCStarGenerator K k)) +
      maximalGroupCStarTrivialCharacter K
        (maximalGroupCStarGenerator K k) •
        (1 - e (f 1)) = ((rhoA k : unitary A) : A)
    rw [hf k, maximalGroupCStarTrivialCharacter_generator]
    have hs : (1 : ℂ) • (1 - e (f 1)) = 1 - e (f 1) :=
      one_smul ℂ _
    rw [hs]
    change e (((rhoC k : unitary C) : C)) +
      (1 - e (f 1)) = ((rhoA k : unitary A) : A)
    rw [map_one, heone, hcorner k]
    have hfix := hfixLeft k
    rw [sub_mul, one_mul, hfix]
    noncomm_ring
  have hLF : L = F :=
    maximalGroupCStar_lift_unique K L F fun k ↦ (hLgen k).trans (hF k).symm
  have hp := DFunLike.congr_fun hLF KD.projection
  change e (f KD.projection) +
      maximalGroupCStarTrivialCharacter K KD.projection • (1 - e (f 1)) =
        F KD.projection at hp
  rw [maximalGroupCStarTrivialCharacter_kazhdanProjection] at hp
  change e (f KD.projection) + (1 : ℂ) • (1 - e (f 1)) =
    F KD.projection at hp
  have hs : (1 : ℂ) • (1 - e (f 1)) = 1 - e (f 1) :=
    one_smul ℂ _
  rw [hs] at hp
  change e (f KD.projection) + (1 - e (f 1)) =
    F KD.projection at hp
  rw [map_one, heone, sub_sub_cancel] at hp
  apply correctedCornerCoronaEmbedHom_injective D (ω : Filter ℕ)
  rw [map_zero]
  apply add_right_cancel (b := F KD.projection)
  simpa only [zero_add] using hp

/-- Projection-zero is preserved when a unitary representation is postcomposed
with a unital star homomorphism. -/
theorem kazhdanProjectionZeroForRepresentation_map
    {K : Type} [Group K] (KD : KazhdanData K)
    {C A : Type*} [CStarAlgebra C] [CStarAlgebra A]
    (rho : K →* unitary C) (j : C →⋆ₐ[ℂ] A)
    (hzero : KazhdanProjectionZeroForRepresentation KD rho) :
    KazhdanProjectionZeroForRepresentation KD ((unitaryMap j).comp rho) := by
  intro F hF
  obtain ⟨f, hf, _⟩ :=
    maximalGroupCStar_existsUnique_lift_allUniverses K rho
  have hjf : j.comp f = F :=
    maximalGroupCStar_lift_unique K (j.comp f) F fun k ↦ by
      change j (f (maximalGroupCStarGenerator K k)) =
        F (maximalGroupCStarGenerator K k)
      rw [hf k]
      exact (hF k).symm
  rw [← hjf, StarAlgHom.comp_apply, hzero f hf, map_zero]

/-! ## Complete provenance assembly -/

/-- The provenance-rich corrected corner sends the maximal Kazhdan projection
to zero after passage to every ultrafilter refining `cofinite`. -/
theorem correctedCornerProvenance_kazhdanProjectionZero
    {G : Type} [Group G] [Countable G]
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (K : Subgroup G) (P : CorrectedCornerProvenanceData G X K)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    CorrectedCornerKazhdanProjectionZero (P.subgroupCorner K) ω hω
      P.kazhdan := by
  let DK := P.subgroupCorner K
  let T : NormMatrixCStarCorona (fun n ↦ X n) →⋆ₐ[ℂ]
      FilterMatrixCStarCorona (fun n ↦ X (P.phi n)) (ω : Filter ℕ) :=
    retainedCoronaToOmega X P.phi P.phi_strictMono ω hω
  let rhoA : K →* unitary
      (ProvenanceRetainedAmbientCorona K P ω) :=
    provenanceRetainedAmbientSubgroupRepresentation K P ω hω
  let FA : MaximalGroupCStar K →⋆ₐ[ℂ]
      ProvenanceRetainedAmbientCorona K P ω :=
    provenanceRetainedAmbientSubgroupLift K P ω hω
  have hFA : ∀ k : K,
      FA (maximalGroupCStarGenerator K k) =
        ((rhoA k : unitary (ProvenanceRetainedAmbientCorona K P ω)) :
          ProvenanceRetainedAmbientCorona K P ω) := by
    exact provenanceRetainedAmbientSubgroupLift_generator K P ω hω
  have hcorner : ∀ k : K,
      correctedCornerCoronaEmbedHom DK (ω : Filter ℕ)
          (((coronaRep (fun n ↦ DK.cornerModel n) ω
            (correctedCornerOmegaRepresentation DK ω hω) k :
              unitary (FilterMatrixCStarCorona
                (fun n ↦ DK.cornerModel n) (ω : Filter ℕ))) :
            FilterMatrixCStarCorona
              (fun n ↦ DK.cornerModel n) (ω : Filter ℕ))) =
        (1 - FA P.kazhdan.projection) *
          ((rhoA k : unitary (FilterMatrixCStarCorona
            (fun n ↦ X (P.phi n)) (ω : Filter ℕ))) :
            FilterMatrixCStarCorona
              (fun n ↦ X (P.phi n)) (ω : Filter ℕ)) := by
    intro k
    have hrestrict :
        coronaRestrictStar X P.phi P.phi_strictMono
            (P.q * ((P.rho (k : G) : unitary
              (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n))) =
          coronaRestrict X P.phi P.phi_strictMono
            (P.q * ((P.rho (k : G) : unitary
              (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n))) :=
      rfl
    have hc := congrArg
      (cofiniteCoronaToOmega (fun n ↦ X (P.phi n)) ω hω)
      (P.subgroupCornerClass K k)
    calc
      correctedCornerCoronaEmbedHom DK (ω : Filter ℕ)
          (((coronaRep (fun n ↦ DK.cornerModel n) ω
            (correctedCornerOmegaRepresentation DK ω hω) k :
              unitary (FilterMatrixCStarCorona
                (fun n ↦ DK.cornerModel n) (ω : Filter ℕ))) :
            FilterMatrixCStarCorona
              (fun n ↦ DK.cornerModel n) (ω : Filter ℕ))) =
          filterMatrixCStarCoronaMk (fun n ↦ X (P.phi n))
            (ω : Filter ℕ) (ambientCornerSeq DK k) := by
              rw [coronaRep_apply]
              change correctedCornerCoronaEmbedHom DK (ω : Filter ℕ)
                  (correctedCornerCoronaGeneratorClass DK ω k) = _
              exact correctedCornerCoronaEmbed_coronaRep DK ω k
      _ = T (P.q * ((P.rho (k : G) : unitary
              (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n))) := by
            rw [← hrestrict] at hc
            change _ = retainedCoronaToOmega X P.phi P.phi_strictMono ω hω
              (P.q * ((P.rho (k : G) : unitary
                (NormMatrixCStarCorona (fun n ↦ X n))) :
                  NormMatrixCStarCorona (fun n ↦ X n)))
            rw [retainedCoronaToOmega, StarAlgHom.comp_apply]
            simpa only [cofiniteCoronaToOmega_mk] using hc
      _ = (1 - FA P.kazhdan.projection) *
          ((rhoA k : unitary (FilterMatrixCStarCorona
            (fun n ↦ X (P.phi n)) (ω : Filter ℕ))) :
            FilterMatrixCStarCorona
              (fun n ↦ X (P.phi n)) (ω : Filter ℕ)) := by
            change T (P.q *
                ((provenanceAmbientSubgroupRepresentation K P k : unitary
              (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n))) =
              (1 - provenanceRetainedAmbientSubgroupLift K P ω hω
                P.kazhdan.projection) *
                T ((provenanceAmbientSubgroupRepresentation K P k : unitary
                  (NormMatrixCStarCorona (fun n ↦ X n))) :
                    NormMatrixCStarCorona (fun n ↦ X n))
            rw [map_mul,
              provenanceRetainedAmbientSubgroupLift_kazhdanProjection_eq_one_sub_q,
              sub_sub_cancel]
  have hzeroCorona := correctedCornerProjectionZero_of_retainedCompression
    DK ω hω P.kazhdan rhoA FA hFA hcorner
  have hzeroOperator := kazhdanProjectionZeroForRepresentation_map P.kazhdan
    (coronaRep (fun n ↦ DK.cornerModel n) ω
      (correctedCornerOmegaRepresentation DK ω hω))
    (cornerCoronaFaithfulRepresentation (fun n ↦ DK.cornerModel n) ω)
    hzeroCorona
  apply correctedCornerKazhdanProjectionZero_of_generic DK ω hω P.kazhdan
  change KazhdanProjectionZeroForRepresentation P.kazhdan
    ((unitaryMap (cornerCoronaFaithfulRepresentation
      (fun n ↦ DK.cornerModel n) ω)).comp
      (coronaRep (fun n ↦ DK.cornerModel n) ω
        (correctedCornerOmegaRepresentation DK ω hω)))
  exact hzeroOperator

/-- The unchanged manuscript hypotheses construct a corrected corner with the
projection-zero compatibility, without strengthening the ambient group to
property `(T)`. -/
theorem exists_correctedCornerKazhdanProjectionZero
    {G : Type} [Group G] [Countable G]
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (K : Subgroup G) [K.Normal]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (KD : KazhdanData K) (k : K)
    (hk : ((rho (k : G) : unitary
      (NormMatrixCStarCorona (fun n ↦ X n))) :
      NormMatrixCStarCorona (fun n ↦ X n)) ≠ 1) :
    ∃ P : CorrectedCornerProvenanceData G X K,
      ∀ (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite),
        CorrectedCornerKazhdanProjectionZero (P.subgroupCorner K) ω hω
          P.kazhdan := by
  obtain ⟨P⟩ := exists_correctedCornerProvenanceData K rho KD k hk
  exact ⟨P, correctedCornerProvenance_kazhdanProjectionZero K P⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
