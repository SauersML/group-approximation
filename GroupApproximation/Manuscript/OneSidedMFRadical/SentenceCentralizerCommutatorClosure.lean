import GroupApproximation.Sofic.KazhdanAsymptoticCommutant

/-!
# The centralizer sequence in the defect-HS proof

This file closes the proof-internal content of sentence-census row 148.  An
exactly commuting pair in the group is sent by an arbitrary operator-norm
almost representation to an operator-norm asymptotically commuting pair of
unitaries.  The same displayed commutator then vanishes in normalized
Hilbert--Schmidt norm.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open KazhdanAsymptoticCommutant KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

universe u v

variable {Gamma : Type v} [Group Gamma]
variable {E : Type u} [Group E]

/-- Exact commutation in the group makes the matrix commutator vanish in
operator norm in every operator-norm almost representation. -/
theorem mapCommutator_opNormVanishing_of_commute
    (B : OpAlmostRepresentation E) {a b : E} (hab : Commute a b) :
    OpNormVanishing B (fun n ↦
      (B.map n a : Matrix (B.model n) (B.model n) ℂ) * B.map n b -
        (B.map n b : Matrix (B.model n) (B.model n) ℂ) * B.map n a) := by
  have habDefect := multiplicativeDefect_vanishing B a b
  have hbaDefect := multiplicativeDefect_vanishing B b a
  have htotal := habDefect.neg.add hbaDefect
  exact htotal.congr fun n ↦ by
    rw [hab.eq]
    noncomm_ring

/-- The operator-norm assertion above in the manuscript's literal
`→ 0` filter notation. -/
theorem mapCommutator_opNorm_tendsto_zero_of_commute
    (B : OpAlmostRepresentation E) {a b : E} (hab : Commute a b) :
    Tendsto (fun n ↦
      ‖(B.map n a : Matrix (B.model n) (B.model n) ℂ) * B.map n b -
        (B.map n b : Matrix (B.model n) (B.model n) ℂ) * B.map n a‖)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := mapCommutator_opNormVanishing_of_commute B hab
    (epsilon / 2) (half_pos hepsilon)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact (hN n hn).trans_lt (half_lt_self hepsilon)

/-- The same matrix commutator is null in normalized Hilbert--Schmidt norm. -/
theorem mapCommutator_hsSqVanishing_of_commute
    (B : OpAlmostRepresentation E) {a b : E} (hab : Commute a b) :
    HSSqVanishing B (fun n ↦
      (B.map n a : Matrix (B.model n) (B.model n) ℂ) * B.map n b -
        (B.map n b : Matrix (B.model n) (B.model n) ℂ) * B.map n a) :=
  HSSqVanishing.of_opNormVanishing
    (mapCommutator_opNormVanishing_of_commute B hab)

/-- Normalized Hilbert--Schmidt vanishing of the commutator in the literal
unsquared form printed in the manuscript. -/
theorem mapCommutator_hsNorm_tendsto_zero_of_commute
    (B : OpAlmostRepresentation E) {a b : E} (hab : Commute a b) :
    Tendsto (fun n ↦ Real.sqrt (hsNormSq (B.model n)
      ((B.map n a : Matrix (B.model n) (B.model n) ℂ) * B.map n b -
        (B.map n b : Matrix (B.model n) (B.model n) ℂ) * B.map n a)))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := mapCommutator_hsSqVanishing_of_commute B hab
    ((epsilon / 2) ^ 2) (sq_pos_of_pos (half_pos hepsilon))
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sqrt (hsNormSq (B.model n)
        ((B.map n a : Matrix (B.model n) (B.model n) ℂ) * B.map n b -
          (B.map n b : Matrix (B.model n) (B.model n) ℂ) * B.map n a))
        ≤ Real.sqrt ((epsilon / 2) ^ 2) :=
      Real.sqrt_le_sqrt (hN n hn)
    _ = epsilon / 2 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (half_pos hepsilon)]
    _ < epsilon := half_lt_self hepsilon

/-- **Sentence-census row 148.**  If `c` centralizes the represented Kazhdan
subgroup, its coordinate matrices asymptotically commute with every subgroup
matrix first in operator norm and then in normalized Hilbert--Schmidt norm. -/
theorem manuscriptSentence148_centralizerSequence
    (B : OpAlmostRepresentation E) (iota : Gamma →* E) (c : E)
    (hc : ∀ gamma : Gamma, Commute c (iota gamma)) :
    ∀ gamma : Gamma,
      Tendsto (fun n ↦
        ‖(B.map n c : Matrix (B.model n) (B.model n) ℂ) *
              B.map n (iota gamma) -
            (B.map n (iota gamma) : Matrix (B.model n) (B.model n) ℂ) *
              B.map n c‖) atTop (nhds 0) ∧
      Tendsto (fun n ↦ Real.sqrt (hsNormSq (B.model n)
        ((B.map n c : Matrix (B.model n) (B.model n) ℂ) *
              B.map n (iota gamma) -
            (B.map n (iota gamma) : Matrix (B.model n) (B.model n) ℂ) *
              B.map n c))) atTop (nhds 0) := by
  intro gamma
  exact ⟨mapCommutator_opNorm_tendsto_zero_of_commute B (hc gamma),
    mapCommutator_hsNorm_tendsto_zero_of_commute B (hc gamma)⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
